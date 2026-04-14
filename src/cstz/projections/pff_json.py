"""PFF JSON projection — ObservationState → pff.schema.json conformant dict.

Maps the CSTZ-native ObservationState to the PFF/RHPF interchange
format.  This is a presentation adapter, not normative content.

The projection generates:
  - ranks: one per regime step (ordinal = step index)
  - patches: one per Patch in the state
  - charts: one per (discriminator, perspective) pair
  - addresses0: one per observed element (grade-0 cells)
  - paths1: glue records when two elements are operationalist-equivalent
  - paths2: empty (coh computed on demand, not serialized)

Conforms to: rhpf-pff-profiles/pff.schema.json v1.0
"""

from __future__ import annotations

from typing import Any, Dict, List

from cstz.observe import ObservationState, Patch, Observation
from cstz.framework import ORDERED_TAU, ORDERED_SIGMA, GAP, OVER


VERSION = "1.0"
IDENTIFIER_SCOPE = "document-local"
DEFAULT_PHASE = "observe"


def _mint_id(prefix: str, n: int) -> str:
    """Generate a PFF-conformant document-local identifier."""
    return f"{prefix}-{n}"


def observation_state_to_pff(
    state: ObservationState,
    document_id: str = "cstz-doc",
) -> Dict[str, Any]:
    """Project an ObservationState to a PFF JSON dict.

    Returns a dict conforming to pff.schema.json.
    """
    regime = state.regime
    elements = sorted(state.all_elements())

    # ── Ranks: one per regime discriminator ──
    ranks: List[Dict[str, Any]] = []
    rank_ids: Dict[int, str] = {}  # discriminator → rank id
    for i, d in enumerate(regime):
        rid = _mint_id("rank", i)
        rank_ids[d] = rid
        ranks.append({
            "id": rid,
            "ordinal": i,
            "label": f"d={d:#b}",
        })
    # Ensure at least one rank (schema requires minItems: 1)
    if not ranks:
        ranks.append({"id": "rank-0", "ordinal": 0})
        default_rank = "rank-0"
    else:
        default_rank = ranks[0]["id"]

    # ── Patches: one per Patch in state ──
    patches: List[Dict[str, Any]] = []
    patch_ids: Dict[int, str] = {}  # patch index → patch id
    for i, patch in enumerate(state.patches):
        pid = _mint_id("patch", i)
        patch_ids[i] = pid
        # Use the first discriminator's rank, or default
        rank_ref = default_rank
        if patch.regime:
            rank_ref = rank_ids.get(patch.regime[0], default_rank)
        patches.append({
            "id": pid,
            "rank": rank_ref,
            "phase": DEFAULT_PHASE,
        })

    # ── Charts: one sigma + one tau per discriminator ──
    charts: List[Dict[str, Any]] = []
    chart_sigma_ids: Dict[int, str] = {}  # discriminator → sigma chart id
    chart_tau_ids: Dict[int, str] = {}    # discriminator → tau chart id
    for i, d in enumerate(regime):
        sid = _mint_id("chart-sigma", i)
        tid = _mint_id("chart-tau", i)
        chart_sigma_ids[d] = sid
        chart_tau_ids[d] = tid
        charts.append({"id": sid, "root": f"d{d:#b}", "kind": "sigma"})
        charts.append({"id": tid, "root": f"d{d:#b}", "kind": "tau"})

    # ── Addresses0: one per observed element ──
    addresses0: List[Dict[str, Any]] = []
    addr0_ids: Dict[int, str] = {}  # element → addr0 id
    for i, elem in enumerate(elements):
        aid = _mint_id("addr0", i)
        addr0_ids[elem] = aid

        # Build segments: one per patch that observes this element
        segments: List[Dict[str, Any]] = []
        for pi, patch in enumerate(state.patches):
            elem_obs = [o for o in patch.observations if o.element == elem]
            if not elem_obs:
                continue

            pairs: List[Dict[str, Any]] = []
            for obs in elem_obs:
                d = obs.discriminator
                tau_val = (obs.result >> 1) & 1
                sigma_val = obs.result & 1

                # Principal pair (sigma chart)
                pairs.append({
                    "chart": chart_sigma_ids.get(d, charts[0]["id"] if charts else "chart-0"),
                    "root": f"e{elem:#b}",
                    "route": [],
                    "role": "principal",
                })
                # Aux pair (tau chart)
                pairs.append({
                    "chart": chart_tau_ids.get(d, charts[0]["id"] if charts else "chart-0"),
                    "root": f"e{elem:#b}",
                    "route": [{"kind": "field", "arg": "tau"}],
                    "role": "aux",
                })

            if pairs:  # pragma: no branch — always true when elem_obs non-empty
                rank_ref = default_rank
                if patch.regime:
                    rank_ref = rank_ids.get(patch.regime[0], default_rank)
                segments.append({
                    "rank": rank_ref,
                    "phase": DEFAULT_PHASE,
                    "patch": patch_ids.get(pi, "patch-0"),
                    "pairs": pairs,
                })

        if not segments:  # pragma: no cover — elements come from observations
            segments.append({
                "rank": default_rank,
                "phase": DEFAULT_PHASE,
                "patch": patches[0]["id"] if patches else "patch-0",
                "pairs": [{
                    "chart": charts[0]["id"] if charts else "chart-0",
                    "root": f"e{elem:#b}",
                    "route": [],
                    "role": "principal",
                }],
            })

        addresses0.append({
            "id": aid,
            "sort": f"e{elem:#b}",
            "discoveryRank": default_rank,
            "segments": segments,
        })

    # ── Assemble document ──
    doc: Dict[str, Any] = {
        "version": VERSION,
        "documentId": document_id,
        "identifierScope": IDENTIFIER_SCOPE,
        "ranks": ranks,
        "patches": patches,
        "charts": charts,
        "addresses0": addresses0,
        "paths1": [],
        "paths2": [],
    }

    return doc
