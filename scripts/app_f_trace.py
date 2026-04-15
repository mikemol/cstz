#!/usr/bin/env python3
"""Appendix F feedback-loop trace with self-applied kappa-evolution.

Three candidate plans for kappa_equiv_batched(pop, regime):

    alpha: naive pairwise (Python loop over pairs).
    beta : dot-batched fingerprint matrix (numpy @ + XOR).
    gamma: packed-bitmask fingerprint (AND + popcount).

Each iteration:
  - measure every plan on every instance;
  - fit cycle->microsecond scaling to plan beta (pivot);
  - compute residues on the other plans;
  - update scalar parameters toward zero residue.

When a plan's residue plateaus (three iterations with <20% improvement
in absolute relative residue), the script runs a *kappa-evolution*:
it fits the remaining residue against a library of candidate
functional forms and adds the best-fitting form as a new parameter
in the dynamic `extras` dict. Subsequent iterations use the extended
parameter space.

This is the framework's residue-consumption dynamic applied to its
own cost model, executed by the script rather than the author.
"""

from __future__ import annotations

import json
import statistics
import time
from dataclasses import asdict, dataclass, field, replace
from typing import Callable

import numpy as np


# ---------------------------------------------------------------------------
# Parameter container (static fields + dynamic extras)
# ---------------------------------------------------------------------------


@dataclass
class Params:
    """Platform parameters; all in symbolic 'cycles' units."""
    w: int = 8
    gamma_launch: int = 4
    l_dot: float = 2.0
    l_xor_reduce: float = 1.0
    l_zeta_pass: float = 1.0
    l_syndrome: float = 1.0
    # Dynamically-discovered parameters: name -> (plan_name, form_name, value)
    # Each form_name maps to a callable in CANDIDATE_FORMS below.
    extras: dict = field(default_factory=dict)


# Library of candidate functional forms for kappa-evolution.
# A new parameter's cost contribution is: value * form(K, n, M).
CANDIDATE_FORMS: dict[str, Callable[[int, int, int], int]] = {
    "per_pair":         lambda K, n, M: K * (K - 1) // 2,
    "per_pair_per_M":   lambda K, n, M: K * (K - 1) // 2 * M,
    "per_element":      lambda K, n, M: K,
    "per_element_per_M": lambda K, n, M: K * M,
    "constant":         lambda K, n, M: 1,
    "per_2n":           lambda K, n, M: 1 << n,
    "per_pair_per_n":   lambda K, n, M: K * (K - 1) // 2 * n,
}


def extras_contribution(params: Params, plan: str, K: int, n: int, M: int) -> float:
    """Sum the contribution of all extras applicable to this plan."""
    total = 0.0
    for name, (tag, form_name, value) in params.extras.items():
        if tag == plan:
            total += value * CANDIDATE_FORMS[form_name](K, n, M)
    return total


# ---------------------------------------------------------------------------
# Cost predictors (MODEL-4 + extras)
# ---------------------------------------------------------------------------


def pred_alpha(p: Params, K: int, n: int, M: int) -> float:
    pairs = K * (K - 1) // 2
    base = p.gamma_launch + pairs * (M * p.l_dot + p.l_xor_reduce)
    return base + extras_contribution(p, "alpha", K, n, M)


def pred_beta(p: Params, K: int, n: int, M: int) -> float:
    warp_passes_dot = M * max(1, K // p.w)
    warp_passes_cmp = (K * K) * max(1, M // p.w) // p.w
    base = p.gamma_launch + warp_passes_dot * p.l_dot + warp_passes_cmp * p.l_xor_reduce
    return base + extras_contribution(p, "beta", K, n, M)


def pred_gamma(p: Params, K: int, n: int, M: int) -> float:
    pack = K + M
    fp_compute = K * M * (p.l_zeta_pass + p.l_syndrome)
    compare = (K * K) * max(1, M // p.w) * p.l_xor_reduce
    base = p.gamma_launch + pack + fp_compute + compare
    return base + extras_contribution(p, "gamma", K, n, M)


PREDICTORS = {"alpha": pred_alpha, "beta": pred_beta, "gamma": pred_gamma}


# ---------------------------------------------------------------------------
# Plan implementations (runnable reference code; unchanged from v1)
# ---------------------------------------------------------------------------


def run_alpha(pop: np.ndarray, regime: np.ndarray) -> np.ndarray:
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
    V = (pop.astype(np.int64) @ regime.T.astype(np.int64)) & 1
    diff = V[:, None, :] ^ V[None, :, :]
    E = (diff.sum(axis=2) == 0).astype(np.uint8)
    return E


def run_gamma(pop: np.ndarray, regime: np.ndarray) -> np.ndarray:
    K, n = pop.shape
    M = regime.shape[0]
    assert n <= 64
    pop_packed = np.zeros(K, dtype=np.uint64)
    for b in range(n):
        pop_packed |= pop[:, b].astype(np.uint64) << np.uint64(b)
    reg_packed = np.zeros(M, dtype=np.uint64)
    for b in range(n):
        reg_packed |= regime[:, b].astype(np.uint64) << np.uint64(b)
    anded = pop_packed[:, None] & reg_packed[None, :]
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
    fn(pop, regime)  # warm-up
    times = []
    for _ in range(runs):
        t0 = time.perf_counter()
        fn(pop, regime)
        t1 = time.perf_counter()
        times.append((t1 - t0) * 1e6)
    return statistics.median(times)


def verify_consistency(pop: np.ndarray, regime: np.ndarray) -> None:
    Ea = run_alpha(pop, regime)
    Eb = run_beta(pop, regime)
    Eg = run_gamma(pop, regime)
    assert np.array_equal(Ea, Eb), "alpha / beta disagree"
    assert np.array_equal(Ea, Eg), "alpha / gamma disagree"


# ---------------------------------------------------------------------------
# Residue computation
# ---------------------------------------------------------------------------


def compute_residues(params: Params, instance_measurements, pivot: str = "beta"):
    """Fit cycle->microsecond scaling on pivot; residues on all plans."""
    rows = []
    for K, n, M, meas in instance_measurements:
        preds = {name: PREDICTORS[name](params, K, n, M) for name in PREDICTORS}
        rows.append({"K": K, "n": n, "M": M, "meas": meas, "preds": preds})

    ratios = [r["meas"][pivot] / r["preds"][pivot] for r in rows if r["preds"][pivot] > 0]
    scale = statistics.median(ratios)

    for r in rows:
        r["scale"] = scale
        r["pred_us"] = {name: r["preds"][name] * scale for name in PREDICTORS}
        r["residue_us"] = {name: r["meas"][name] - r["pred_us"][name] for name in PREDICTORS}
        # Use |pred_us| in the denominator so negative predictions (parameter
        # overcorrection) produce honest large-magnitude residues instead of
        # silently clipping to zero.
        r["residue_rel"] = {
            name: (r["meas"][name] - r["pred_us"][name]) / abs(r["pred_us"][name])
                   if r["pred_us"][name] != 0 else float("inf")
            for name in PREDICTORS
        }
    return rows, scale


# ---------------------------------------------------------------------------
# Plateau detection and kappa-evolution
# ---------------------------------------------------------------------------


def detect_stuck(history: list[float], min_iters: int = 3, threshold: float = 0.50) -> bool:
    """True if |residue| has stayed above threshold for min_iters iterations.

    This is the 'residue refuses to close' signature: scalar parameter
    updates have been applied for min_iters iterations yet the residue
    magnitude remains > threshold. In [DAF] four-cell terms, this
    signals that the current kappa cannot consume the residue; a new
    discriminator must be articulated.
    """
    if len(history) < min_iters:
        return False
    return all(abs(r) > threshold for r in history[-min_iters:])


def detect_overdetermination(plan: str, rows) -> bool:
    """Four-cell (1,1) signature: residue flips sign across instances.

    After a kappa-evolution adds a new extra, if the new parameter's
    form is linearly correlated with an existing term, the combined
    prediction over-closes the residue at some instances and
    under-closes at others. The empirical signature is opposite signs
    of residue_rel across instances with at least one of significant
    magnitude.
    """
    residues = [r["residue_rel"][plan] for r in rows]
    if all(abs(r) < 0.20 for r in residues):
        return False
    has_pos = any(r > 0.30 for r in residues)
    has_neg = any(r < -0.30 for r in residues)
    return has_pos and has_neg


# Per-plan base forms: (name, form_callable, value_extractor).
# Each base form is one term that appears in the plan's predictor
# with a known functional shape and parameter dependence.
BASE_FORMS: dict[str, list] = {
    "alpha": [
        ("l_dot x per_pair_per_M",
         lambda K, n, M: K * (K - 1) // 2 * M,
         lambda p: p.l_dot),
        ("l_xor x per_pair",
         lambda K, n, M: K * (K - 1) // 2,
         lambda p: p.l_xor_reduce),
    ],
    "beta": [
        ("l_dot x M*ceil(K/w)",
         lambda K, n, M: M * max(1, K // 8),
         lambda p: p.l_dot),
        ("l_xor x compare",
         lambda K, n, M: (K * K) * max(1, M // 8) // 8,
         lambda p: p.l_xor_reduce),
    ],
    "gamma": [
        ("(l_zeta+l_syn) x K*M",
         lambda K, n, M: K * M,
         lambda p: p.l_zeta_pass + p.l_syndrome),
        ("l_xor x compare",
         lambda K, n, M: (K * K) * max(1, M // 8),
         lambda p: p.l_xor_reduce),
    ],
}


def collect_contributions(plan: str, params: Params):
    """Enumerate every form contributing to plan's prediction.

    Returns list of (name, form_fn, current_value) tuples.
    """
    result = []
    for name, form_fn, value_fn in BASE_FORMS.get(plan, []):
        result.append((name, form_fn, value_fn(params)))
    for extra_name, (tag, form_name, value) in params.extras.items():
        if tag == plan:
            result.append((extra_name, CANDIDATE_FORMS[form_name], value))
    return result


def analyze_blade(plan: str, params: Params, rows):
    """SVD-based diagnostic of the plan's parameter-space blade.

    Constructs the instance-contribution matrix M where M[i, j] is the
    per-instance value of contribution j at instance i (already scaled
    by its current parameter value). Returns (contributions, M, S, Vt)
    where S is the singular spectrum and Vt the right singular vectors.
    """
    contribs = collect_contributions(plan, params)
    if len(contribs) < 2:
        return contribs, None, None, None
    M = np.array(
        [[f(r["K"], r["n"], r["M"]) for (_, f, _) in contribs] for r in rows],
        dtype=float,
    )
    if M.shape[0] < M.shape[1]:
        # underdetermined: not enough instances to fit all params
        return contribs, M, None, None
    U, S, Vt = np.linalg.svd(M, full_matrices=False)
    return contribs, M, S, Vt


def orthogonalize_blade(
    plan: str, params: Params, rows, tol: float = 0.15
) -> tuple[Params, bool, str]:
    """Detect and resolve rank-deficient blades in the plan's parameter space.

    If SVD reveals a near-zero singular value (sigma_min / sigma_max < tol),
    the participating forms are linearly dependent at the observed instances:
    the blade p_1 ∧ ... ∧ p_k has rank < k.  The resolution (Hodge
    complement / principal-direction retention) is implemented as: drop
    the extra parameter whose column has the largest projection onto the
    degenerate right-singular-vector direction.  Base parameters are
    preserved (their forms are structural to the predictor; only extras
    are disposable).

    Returns (new_params, did_orthogonalize, diagnostic_message).
    """
    contribs, M, S, Vt = analyze_blade(plan, params, rows)
    if S is None:
        return params, False, f"plan={plan}: blade analysis skipped (too few contribs / instances)"

    ratio = S[-1] / S[0] if S[0] > 0 else 1.0
    lines = [
        f"plan={plan}: singular values = {S.round(3).tolist()}  "
        f"(sigma_min/sigma_max = {ratio:.3f})"
    ]
    for j, (name, _, v) in enumerate(contribs):
        proj = Vt[-1, j]  # projection onto the smallest singular direction
        lines.append(
            f"    contrib[{j}] {name!r}: value={v:+.4f}, "
            f"V[last, {j}] = {proj:+.3f}"
        )

    if ratio >= tol:
        lines.append("    verdict: full-rank; residue is not collinearity")
        return params, False, "\n  ".join(lines)

    # Rank deficient. Find the extra whose contribution projects most
    # strongly onto the degenerate direction.
    extras_indices = [
        j for j, (name, _, _) in enumerate(contribs) if name in params.extras
    ]
    if not extras_indices:
        lines.append("    verdict: rank-deficient but only base params participate; cannot drop")
        return params, False, "\n  ".join(lines)

    worst = max(extras_indices, key=lambda j: abs(Vt[-1, j]))
    worst_name = contribs[worst][0]
    dropped_form = params.extras[worst_name][1]  # form_name
    lines.append(f"    verdict: rank-deficient; dropping extra {worst_name!r} (form={dropped_form})")
    new_extras = {k: v for k, v in params.extras.items() if k != worst_name}
    return replace(params, extras=new_extras), True, "\n  ".join(lines)


def suggest_kappa_evolution(
    plan: str,
    scale_us_per_cycle: float,
    rows,
    exclude: set[str] | None = None,
) -> tuple[str, str, float] | None:
    """Fit plan's residue against each candidate form; pick best fit.

    Returns (extra_name, form_name, value_in_cycles) or None if no
    candidate form has consistent ratios across instances. Forms in
    `exclude` are skipped (used for avoiding previously-forbidden forms).
    """
    exclude = exclude or set()
    best = None
    best_cv = float("inf")
    for form_name, form in CANDIDATE_FORMS.items():
        if form_name in exclude:
            continue
        vals = []
        for r in rows:
            K, n, M = r["K"], r["n"], r["M"]
            form_val = form(K, n, M)
            if form_val == 0:
                break
            # residue in *cycles* (divide by scale_us_per_cycle)
            residue_cycles = r["residue_us"][plan] / scale_us_per_cycle
            vals.append(residue_cycles / form_val)
        else:
            if not vals:
                continue
            mean_val = statistics.mean(vals)
            if mean_val == 0:
                continue  # form doesn't explain the residue
            if len(vals) > 1:
                stdev_val = statistics.stdev(vals)
                cv = stdev_val / abs(mean_val)  # coefficient of variation
            else:
                cv = 0.0
            # Negative mean is fine: corresponds to an over-prediction and
            # a negative-valued extra (i.e., subtract this term from pred).
            if cv < best_cv:
                best_cv = cv
                best = (form_name, mean_val, cv)
    if best is None or best_cv > 0.5:
        return None
    form_name, value, cv = best
    extra_name = f"l_{plan}_{form_name}"
    return (extra_name, form_name, value)


def update_params(
    params: Params,
    rows,
    plateau_history: dict[str, list[float]],
    forbidden_forms: dict[str, set] | None = None,
):
    """Scalar updates, kappa-evolution on stuck residue, blade orthogonalization on overdetermination."""

    def mean_res(name):
        vals = [r["residue_rel"][name] for r in rows]
        return statistics.mean(vals) if vals else 0.0

    ra = mean_res("alpha")
    rg = mean_res("gamma")

    plateau_history.setdefault("alpha", []).append(ra)
    plateau_history.setdefault("gamma", []).append(rg)

    new_params = params
    kappa_evolved = False

    forbidden_forms = forbidden_forms if forbidden_forms is not None else {}

    # Blade orthogonalization: four-cell (1,1) signature check, per plan.
    # Run this *before* kappa-evolution so that a freshly-degenerate
    # extra gets cleaned up before a new one is added on top.
    for plan in ("alpha", "beta", "gamma"):
        if detect_overdetermination(plan, rows):
            pre_extras_forms = {e[1] for e in new_params.extras.values() if e[0] == plan}
            new_params, did_orth, diag = orthogonalize_blade(plan, new_params, rows)
            print(f"  [overdetermination] {diag}")
            if did_orth:
                # Record dropped forms as forbidden for future kappa-evolutions.
                # Do NOT clear plateau_history: the residue was present before the
                # dropped extra was added, so the history accurately reflects that
                # the current (post-drop) parameter space still can't consume it.
                post_extras_forms = {e[1] for e in new_params.extras.values() if e[0] == plan}
                dropped = pre_extras_forms - post_extras_forms
                forbidden_forms.setdefault(plan, set()).update(dropped)
                kappa_evolved = True

    # Stuck-residue check + kappa-evolution on alpha and gamma
    new_extras = dict(new_params.extras)
    for plan in ("alpha", "gamma"):
        plan_res = ra if plan == "alpha" else rg
        if detect_stuck(plateau_history[plan], min_iters=3, threshold=0.30):
            scale = rows[0]["scale"]
            suggestion = suggest_kappa_evolution(plan, scale, rows)
            if suggestion:
                extra_name, form_name, value = suggestion
                existing_forms = {e[1] for e in new_extras.values() if e[0] == plan}
                forbidden = forbidden_forms.get(plan, set())
                if form_name in forbidden:
                    # Best-fit form already known to be rank-deficient;
                    # try the next-best non-forbidden form.
                    alt = suggest_kappa_evolution(plan, scale, rows, exclude=existing_forms | forbidden)
                    if alt is None:
                        print(f"  [kappa-evolution] {plan} residue stuck at {plan_res:+.1%} "
                              f"but all candidate forms are exhausted or forbidden")
                        continue
                    extra_name, form_name, value = alt
                if form_name not in existing_forms:
                    print(f"  [kappa-evolution] {plan} residue stuck at {plan_res:+.1%} "
                          f"for >=3 iters; adding extra {extra_name!r} = "
                          f"{value:.3f} cycles per {form_name}")
                    new_extras[extra_name] = (plan, form_name, value)
                    plateau_history[plan].clear()
                    kappa_evolved = True

    # Scalar update on gamma (l_zeta_pass)
    delta = 0.25
    l_zeta_new = max(0.25, new_params.l_zeta_pass + delta * rg)

    updated = replace(
        new_params,
        l_zeta_pass=round(l_zeta_new, 3),
        extras=new_extras,
    )
    return updated, kappa_evolved


# ---------------------------------------------------------------------------
# Top-level feedback loop
# ---------------------------------------------------------------------------


def feedback_loop(instances_spec, max_iterations: int = 12):
    np.random.seed(42)
    materialized = []
    for K, n, M in instances_spec:
        pop = np.random.randint(0, 2, (K, n), dtype=np.uint8)
        regime = np.random.randint(0, 2, (M, n), dtype=np.uint8)
        verify_consistency(pop, regime)
        materialized.append((K, n, M, pop, regime))

    params = Params()
    plateau_history = {}
    # Track (plan, form_name) pairs that orthogonalization has dropped so
    # that subsequent kappa-evolutions avoid re-adding the same redundant form.
    forbidden_forms: dict[str, set] = {}
    log = []

    for it in range(max_iterations):
        # Measure every instance
        instance_measurements = []
        for K, n, M, pop, regime in materialized:
            meas = {name: bench(RUNNERS[name], pop, regime) for name in RUNNERS}
            instance_measurements.append((K, n, M, meas))

        rows, scale = compute_residues(params, instance_measurements)

        print(f"\n===== ITERATION {it} =====")
        print(f"params: l_dot={params.l_dot}, l_zeta_pass={params.l_zeta_pass}, "
              f"extras={list(params.extras.keys())}")
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

        log.append({
            "iteration": it,
            "params": {
                **{k: v for k, v in asdict(params).items() if k != "extras"},
                "extras": params.extras,
            },
            "cycle_us": scale,
            "rows": rows,
        })

        if it < max_iterations - 1:
            new_params, kappa_evolved = update_params(
                params, rows, plateau_history, forbidden_forms
            )
            # Convergence check: every residue within ±15% on every instance.
            max_abs_res = max(
                abs(r["residue_rel"][p]) for r in rows for p in ("alpha", "gamma")
            )
            if max_abs_res < 0.15:
                print(f"\n(all alpha/gamma residues within ±15% per-instance; converged at iter {it})")
                break
            if new_params == params and not kappa_evolved:
                print(f"\n(params stable at iteration {it}; nothing more to try)")
                break
            params = new_params

    return log


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    instances = [
        (8, 3, 3),
        (32, 4, 4),
        (64, 5, 5),
    ]
    log = feedback_loop(instances, max_iterations=12)

    print("\n===== TRACE JSON =====")
    # Custom default to handle frozen tuples in extras
    def default(o):
        if isinstance(o, tuple):
            return list(o)
        return float(o)
    print(json.dumps(log, indent=2, default=default))


if __name__ == "__main__":
    main()
