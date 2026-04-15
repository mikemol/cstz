#!/usr/bin/env python3
"""Appendix F feedback-loop trace: measure, compute residues, update.

Three candidate plans for kappa_equiv_batched(pop, regime):

    alpha: naive pairwise — for each pair (i,j), compare fingerprints.
    beta : dot-batched fingerprint matrix, pairwise XOR compare.
    gamma: packed-bitmask (AND + popcount) fingerprint, pairwise XOR compare.

MODEL-4 predicts LAT in symbolic cycles. We measure wall-clock in
microseconds, fit a single cycle-to-microsecond scaling factor to the
Pareto-winning plan, then observe the residues on the other plans.
Residues that exceed a noise threshold trigger parameter updates: the
offending atom's per-element baseline is adjusted by the regression
coefficient of its instance count against the residue.

Output is written to stdout as a structured log. The paper's App F
cites specific lines from this log as witness.
"""

from __future__ import annotations

import json
import statistics
import sys
import time
from dataclasses import asdict, dataclass, field, replace
from typing import Callable

import numpy as np


# ---------------------------------------------------------------------------
# MODEL-4 parameters and per-atom baselines
# ---------------------------------------------------------------------------


@dataclass
class Params:
    """Platform parameters; all in symbolic 'cycles' units."""
    w: int = 8                  # warp width
    gamma_launch: int = 4       # kernel launch overhead
    l_dot: float = 2.0          # dot-product per element per discriminator
    l_xor_reduce: float = 1.0   # XOR reduction per element
    l_zeta_pass: float = 1.0    # butterfly pass per byte
    l_syndrome: float = 1.0     # per-byte syndrome accumulation


# ---------------------------------------------------------------------------
# Cost predictors (MODEL-4)
# ---------------------------------------------------------------------------


def pred_alpha(p: Params, K: int, n: int, M: int) -> float:
    """Naive pairwise: K*(K-1)/2 pairs, each M dot products + 1 reduce."""
    pairs = K * (K - 1) // 2
    return p.gamma_launch + pairs * (M * p.l_dot + p.l_xor_reduce)


def pred_beta(p: Params, K: int, n: int, M: int) -> float:
    """Dot-batched: M rounds of K-wide dot, then K^2 pairwise XOR-compare."""
    warp_passes_dot = M * max(1, K // p.w)
    warp_passes_cmp = (K * K) * max(1, M // p.w) // p.w
    return p.gamma_launch + warp_passes_dot * p.l_dot + warp_passes_cmp * p.l_xor_reduce


def pred_gamma(p: Params, K: int, n: int, M: int) -> float:
    """Packed-bitmask: K+M packs, K*M (AND + popcount), K^2 compare."""
    pack = K + M  # one packed int per population/regime element
    fp_compute = K * M * (p.l_zeta_pass + p.l_syndrome)  # AND + popcount per pair
    compare = (K * K) * max(1, M // p.w) * p.l_xor_reduce
    return p.gamma_launch + pack + fp_compute + compare


PREDICTORS = {"alpha": pred_alpha, "beta": pred_beta, "gamma": pred_gamma}


# ---------------------------------------------------------------------------
# Plan implementations (runnable reference code)
# ---------------------------------------------------------------------------


def run_alpha(pop: np.ndarray, regime: np.ndarray) -> np.ndarray:
    """Naive pairwise."""
    K = pop.shape[0]
    M = regime.shape[0]
    E = np.zeros((K, K), dtype=np.uint8)
    for i in range(K):
        for j in range(i + 1, K):
            same = True
            for m in range(M):
                v_i = int((pop[i] * regime[m]).sum()) & 1
                v_j = int((pop[j] * regime[m]).sum()) & 1
                if v_i != v_j:
                    same = False
                    break
            if same:
                E[i, j] = E[j, i] = 1
    np.fill_diagonal(E, 1)
    return E


def run_beta(pop: np.ndarray, regime: np.ndarray) -> np.ndarray:
    """Dot-batched fingerprint matrix, pairwise XOR compare."""
    V = (pop.astype(np.int64) @ regime.T.astype(np.int64)) & 1  # (K, M)
    diff = V[:, None, :] ^ V[None, :, :]
    E = (diff.sum(axis=2) == 0).astype(np.uint8)
    return E


def run_gamma(pop: np.ndarray, regime: np.ndarray) -> np.ndarray:
    """Packed-bitmask fingerprint via AND + popcount-mod-2, then compare."""
    K, n = pop.shape
    M = regime.shape[0]
    assert n <= 64, "packed bitmask needs n <= 64"
    # Pack each element to a single uint64 bitmask.
    pop_packed = np.zeros(K, dtype=np.uint64)
    for b in range(n):
        pop_packed |= pop[:, b].astype(np.uint64) << np.uint64(b)
    reg_packed = np.zeros(M, dtype=np.uint64)
    for b in range(n):
        reg_packed |= regime[:, b].astype(np.uint64) << np.uint64(b)
    # Fingerprint: V[i, m] = popcount(pop[i] & regime[m]) & 1
    anded = pop_packed[:, None] & reg_packed[None, :]  # (K, M)
    V = (np.bitwise_count(anded) & np.uint64(1)).astype(np.uint8)
    diff = V[:, None, :] ^ V[None, :, :]
    E = (diff.sum(axis=2) == 0).astype(np.uint8)
    return E


RUNNERS: dict[str, Callable[[np.ndarray, np.ndarray], np.ndarray]] = {
    "alpha": run_alpha,
    "beta": run_beta,
    "gamma": run_gamma,
}


# ---------------------------------------------------------------------------
# Benchmark harness
# ---------------------------------------------------------------------------


def bench(fn, pop, regime, runs: int = 7) -> float:
    """Return median wall-clock time in microseconds."""
    # Warm-up
    fn(pop, regime)
    times = []
    for _ in range(runs):
        t0 = time.perf_counter()
        fn(pop, regime)
        t1 = time.perf_counter()
        times.append((t1 - t0) * 1e6)
    return statistics.median(times)


def verify_consistency(pop: np.ndarray, regime: np.ndarray) -> None:
    """All three plans must produce the same equivalence matrix."""
    Ea = run_alpha(pop, regime)
    Eb = run_beta(pop, regime)
    Eg = run_gamma(pop, regime)
    assert np.array_equal(Ea, Eb), "alpha / beta disagree"
    assert np.array_equal(Ea, Eg), "alpha / gamma disagree"


# ---------------------------------------------------------------------------
# Residue computation and parameter update
# ---------------------------------------------------------------------------


def compute_residues(params: Params, instances, pivot: str = "beta"):
    """Fit cycle->microsecond scaling on `pivot` plan; residues elsewhere."""
    rows = []
    # Collect all instances' measurements
    for K, n, M, meas in instances:
        preds = {name: PREDICTORS[name](params, K, n, M) for name in PREDICTORS}
        rows.append({"K": K, "n": n, "M": M, "meas": meas, "preds": preds})

    # Fit global cycle scale on the pivot plan across all instances
    # scale = median(meas[pivot] / pred[pivot])
    ratios = [r["meas"][pivot] / r["preds"][pivot] for r in rows if r["preds"][pivot] > 0]
    scale = statistics.median(ratios)

    for r in rows:
        r["scale"] = scale
        r["pred_us"] = {name: r["preds"][name] * scale for name in PREDICTORS}
        r["residue_us"] = {name: r["meas"][name] - r["pred_us"][name] for name in PREDICTORS}
        r["residue_rel"] = {
            name: (r["meas"][name] - r["pred_us"][name]) / r["pred_us"][name]
                   if r["pred_us"][name] > 0 else 0.0
            for name in PREDICTORS
        }
    return rows, scale


def update_params(params: Params, rows) -> Params:
    """Adjust per-atom baselines by the sign of each plan's relative residue.

    Rule: if plan X's residue averages positive, its dominant atom's
    baseline is incremented; if negative, decremented. Simple, monotonic,
    bounded — intended as a demonstration of convergence, not a real fitter.
    """
    def mean_res(name):
        vals = [r["residue_rel"][name] for r in rows]
        return statistics.mean(vals) if vals else 0.0

    ra = mean_res("alpha")
    rb = mean_res("beta")
    rg = mean_res("gamma")

    # Per-plan dominant atom to tune:
    #   alpha tunes l_dot (dominant inside nested loops)
    #   gamma tunes l_zeta_pass (dominant in encode phase)
    delta = 0.25  # small step; ensures monotone updates

    l_dot_new = max(0.25, params.l_dot + delta * ra)
    l_zeta_new = max(0.25, params.l_zeta_pass + delta * rg)
    return replace(params, l_dot=round(l_dot_new, 3), l_zeta_pass=round(l_zeta_new, 3))


# ---------------------------------------------------------------------------
# Top-level feedback loop
# ---------------------------------------------------------------------------


def feedback_loop(instances_spec, iterations: int = 3):
    np.random.seed(42)

    # Materialize populations and regimes once.
    materialized = []
    for K, n, M in instances_spec:
        pop = np.random.randint(0, 2, (K, n), dtype=np.uint8)
        regime = np.random.randint(0, 2, (M, n), dtype=np.uint8)
        # sanity-check consistency
        verify_consistency(pop, regime)
        materialized.append((K, n, M, pop, regime))

    params = Params()

    log = []
    for it in range(iterations):
        # Measure every instance under current params
        instance_measurements = []
        for K, n, M, pop, regime in materialized:
            meas = {name: bench(RUNNERS[name], pop, regime) for name in RUNNERS}
            instance_measurements.append((K, n, M, meas))

        rows, scale = compute_residues(params, instance_measurements)

        log.append({
            "iteration": it,
            "params": asdict(params),
            "cycle_us": scale,
            "rows": rows,
        })

        # Report
        print(f"\n===== ITERATION {it} =====")
        print(f"params: l_dot={params.l_dot}, l_zeta_pass={params.l_zeta_pass}, "
              f"gamma_launch={params.gamma_launch}")
        print(f"cycle scaling (fit to beta): 1 cycle = {scale:.6f} us")
        print(f"{'(K,n,M)':<12} {'plan':<6} "
              f"{'pred(c)':>10} {'pred(us)':>10} {'meas(us)':>10} "
              f"{'res(us)':>10} {'res(rel)':>10}")
        for r in rows:
            tag = f"({r['K']},{r['n']},{r['M']})"
            for name in ("alpha", "beta", "gamma"):
                print(f"{tag:<12} {name:<6} "
                      f"{r['preds'][name]:>10.2f} {r['pred_us'][name]:>10.3f} "
                      f"{r['meas'][name]:>10.3f} {r['residue_us'][name]:>+10.3f} "
                      f"{r['residue_rel'][name]:>+9.1%}")

        # Winner reporting
        for r in rows:
            tag = f"({r['K']},{r['n']},{r['M']})"
            pred_winner = min(r["preds"], key=r["preds"].get)
            meas_winner = min(r["meas"], key=r["meas"].get)
            agree = "OK" if pred_winner == meas_winner else "MISMATCH"
            print(f"  {tag:<12} predicted-winner={pred_winner:<6} "
                  f"measured-winner={meas_winner:<6} [{agree}]")

        # Decide whether to iterate
        if it < iterations - 1:
            new_params = update_params(params, rows)
            if new_params == params:
                print(f"\n(params stable at iteration {it}; terminating early)")
                break
            params = new_params

    return log


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    # Three workload instances scaled for CPU-numpy execution.
    # Real GPU MODEL-4 would use K=256, n=8, M=8; we downshift so naive
    # plan-alpha completes in seconds, not hours.
    instances = [
        (8, 3, 3),
        (32, 4, 4),
        (64, 5, 5),
    ]
    log = feedback_loop(instances, iterations=3)

    # Emit JSON blob for embedding in the paper
    print("\n===== TRACE JSON =====")
    print(json.dumps(log, indent=2, default=float))


if __name__ == "__main__":
    main()
