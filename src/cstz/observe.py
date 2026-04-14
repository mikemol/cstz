"""Observation protocol — CSTZ-native ingest, merge, and query.

An observation is a discrimination: (element, discriminator, result).
All three are bitvectors. The result is in Ω = GF(2)².  There is
no other type of data.  Gluing witnesses, property observations,
structural annotations — all observations.

A patch is a set of observations sharing a regime context.  Patches
are orthogonal where their observation domains don't overlap.  Where
they overlap, profiles accumulate (componentwise OR on Ω).

The observation protocol enforces:
  - S₃ symmetry: no hardcoded perspective ordering
  - Operationalist equivalence: no union-find, computed at query time
  - Regime monotonicity (WF-1): evolutions only append
  - Profile accumulation: merge by OR, no rejection

Mirrors: agda/CSTZ/ (the full algebraic kernel)
Replaces: legacy/pff.py + legacy/pff_cascade.py cascade semantics

Cofibration (STUDY.md §8.3, Python cofiber): this module has no direct
Agda counterpart. The sheaf-of-discriminations semantics is fixed in
``agda/CSTZ/Topos/Sheaves.agda``, but the *state carrier* that
accumulates observations at runtime — ``Observation``, ``Patch``,
``ObservationState`` — is runtime-only by design. The four invariants
enforced here (S₃ symmetry, operationalist equivalence via
:func:`cstz.sets.kappa_equiv`, regime monotonicity, OR-accumulation of
profiles) are the operational expression of the sheaf axioms.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Iterator, List, Optional, Set, Tuple

from cstz.gf2 import dot, popcount, vec_add
from cstz.framework import (
    CellKind, classify, chi, is_residue, is_boolean,
    GAP, ORDERED_TAU, ORDERED_SIGMA, OVER,
)
from cstz.higher import Perspective


# ---------------------------------------------------------------------------
# Core types
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Observation:
    """A single discrimination result.

    An observation records: discriminator d was applied to element a,
    producing profile result r ∈ Ω = GF(2)².

    The element, discriminator, and result are all bitvectors.
    The representation IS the identity — no string ids needed.
    """
    element: int        # bitvector — population element
    discriminator: int  # bitvector — the discriminator applied
    result: int         # 2-bit Ω value (packed: tau<<1 | sigma)


@dataclass
class Patch:
    """A set of observations with a regime context.

    A patch represents one party's observations over a shared
    population.  The regime records which discriminators are in play.
    Observations within a patch are orthogonal to observations in
    other patches where their domains don't overlap.

    Patches are the CSTZ-native replacement for PFF's Segments,
    Ranks, and Patches — unified into one concept.
    """
    regime: List[int] = field(default_factory=list)
    observations: List[Observation] = field(default_factory=list)

    def observe(self, element: int, discriminator: int, result: int) -> Observation:
        """Record an observation.  Adds discriminator to regime if new."""
        if discriminator not in self.regime:
            self.regime.append(discriminator)
        obs = Observation(element=element, discriminator=discriminator, result=result)
        self.observations.append(obs)
        return obs

    def observe_with_eval(self, eval_fn, d_tau: int, d_sigma: int, element: int) -> Observation:
        """Compute and record an observation from an eval function.

        Applies both τ and σ discriminators to the element, producing
        a 2-bit profile result.
        """
        tau_val = eval_fn(d_tau, element)
        sigma_val = eval_fn(d_sigma, element)
        result = (tau_val << 1) | sigma_val
        return self.observe(element, d_tau, result)

    @property
    def dim(self) -> int:
        """Dimension of this patch's regime."""
        return len(self.regime)

    def elements(self) -> Set[int]:
        """All elements observed in this patch."""
        return {obs.element for obs in self.observations}

    def discriminators(self) -> Set[int]:
        """All discriminators used in this patch."""
        return {obs.discriminator for obs in self.observations}


# ---------------------------------------------------------------------------
# Observation state — the complete discrimination state
# ---------------------------------------------------------------------------


@dataclass
class ObservationState:
    """The complete discrimination state across all patches.

    This is the CSTZ-native replacement for PFF's Document +
    PFFCascadeEngine.  It holds all observations and computes
    algebraic properties on demand from the kernel.

    No union-find.  No hash-cons.  No cascade worklist.
    Equivalence is operationalist: computed at query time.
    """
    dim: int
    patches: List[Patch] = field(default_factory=list)

    # ── Patch management ────────────────────────────────────────

    def new_patch(self) -> Patch:
        """Create and register a new empty patch."""
        p = Patch()
        self.patches.append(p)
        return p

    def merge(self, patch: Patch) -> None:
        """Merge an external patch into this state.

        Merge is append: observations accumulate, regimes grow.
        No consistency check — profiles accumulate via OR on Ω.
        This is not a design shortcut; it's the correct semantics:
        gap + anything = that thing; overlap is valid information.
        """
        self.patches.append(patch)

    # ── Regime ──────────────────────────────────────────────────

    @property
    def regime(self) -> List[int]:
        """The combined regime across all patches (union of discriminators)."""
        seen: Set[int] = set()
        result: List[int] = []
        for patch in self.patches:
            for d in patch.regime:
                if d not in seen:
                    seen.add(d)
                    result.append(d)
        return result

    @property
    def regime_dim(self) -> int:
        """Dimension of the combined regime."""
        return len(self.regime)

    # ── Profile queries ─────────────────────────────────────────

    def profile(self, element: int) -> int:
        """Accumulated Ω profile of element across all patches.

        Accumulation is componentwise OR: each observation
        contributes its result, and results OR together.
        Gap (0) is identity under OR; overlap (3) dominates.
        """
        accumulated = GAP  # 0b00
        for patch in self.patches:
            for obs in patch.observations:
                if obs.element == element:
                    accumulated |= obs.result
        return accumulated

    def profile_under(self, element: int, discriminator: int) -> int:
        """Profile of element under a specific discriminator."""
        accumulated = GAP
        for patch in self.patches:
            for obs in patch.observations:
                if obs.element == element and obs.discriminator == discriminator:
                    accumulated |= obs.result
        return accumulated

    # ── Equivalence (operationalist) ────────────────────────────

    def equiv(self, a: int, b: int) -> bool:
        """Operationalist equivalence: a and b are equivalent iff
        no discriminator in the combined regime separates them.

        Two elements are separated if they have different accumulated
        profiles under some discriminator.
        """
        for d in self.regime:
            if self.profile_under(a, d) != self.profile_under(b, d):
                return False
        return True

    # ── Classification ──────────────────────────────────────────

    def classify_element(self, element: int) -> CellKind:
        """Four-cell classification of element's accumulated profile."""
        return classify(self.profile(element))

    def residue_elements(self) -> Set[int]:
        """All elements with χ = 0 (gap or overlap) in accumulated profile."""
        return {e for e in self.all_elements() if is_residue(self.profile(e))}

    def boolean_elements(self) -> Set[int]:
        """All elements with χ = 1 (ordered-τ or ordered-σ)."""
        return {e for e in self.all_elements() if is_boolean(self.profile(e))}

    # ── Element inventory ───────────────────────────────────────

    def all_elements(self) -> Set[int]:
        """All elements observed across all patches."""
        return {obs.element for patch in self.patches for obs in patch.observations}

    # ── Equivalence classes ─────────────────────────────────────

    def equivalence_classes(self) -> Dict[int, Set[int]]:
        """Partition all elements into equivalence classes.

        Two elements are in the same class iff equiv(a, b).
        Uses the combined regime's profile as the class key.
        """
        classes: Dict[int, Set[int]] = {}
        for elem in self.all_elements():
            # Class key: tuple of profiles under each regime discriminator
            key = tuple(self.profile_under(elem, d) for d in self.regime)
            # Use hash of key as dict key (profiles are small ints)
            h = hash(key)
            if h not in classes:
                classes[h] = set()
            classes[h].add(elem)
        return classes
