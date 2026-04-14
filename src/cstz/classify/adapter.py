"""Adapter — the semantic projection from Classified to Observation.

The adapter is the ONLY place where a τ-vector becomes Observation
triples.  The mapping is injective (one fired discriminator →
exactly one Observation) and monotone (τ'⊇τ produces a superset of
observations).

No inference, no normalization, no filtering.  σ observations are
never emitted: τ=0 is silence, not falsehood (operationalist axiom).
"""

from __future__ import annotations

from typing import Iterable, Tuple

from cstz.classify.base import Classified
from cstz.framework import ORDERED_TAU
from cstz.observe import Patch


def emit_patch(
    items: Iterable[Tuple[int, Classified]],
    patch: Patch,
) -> None:
    """Project classified walk output into a Patch.

    For each (zpath, Classified), emit one Observation per fired
    discriminator bit:

        Observation(element=zpath, discriminator=d_id,
                    result=ORDERED_TAU)

    The element IS the zpath (the bitvector encoding of the path
    from the anchor).  The discriminator IS the one-hot bit of the
    fired discriminator.  Only ORDERED_TAU is emitted — σ is silence.

    Side-effects: appends to `patch.observations` and `patch.regime`.
    The patch is modified in place.

    Silence: if Classified.tau == 0, no observations are emitted
    (operationalist axiom: τ=0 means silence, not falsehood).
    """
    for zp, c in items:
        d = c.tau
        while d:
            lo = d & -d           # isolate lowest set bit
            patch.observe(zp, lo, ORDERED_TAU)
            d ^= lo               # clear it, advance
