"""Classifier base types — Classified, ShapeWitness, Classifier.

A classifier projects a subset of registered discriminators onto
input nodes.  The output (Classified) contains:

  - τ: bitmask of fired discriminators (identity)
  - shape: local binarized arity and role names

σ is implicit: it is the complement of τ relative to the classifier's
discriminator_ids.  This module never emits or stores σ.

Invariants enforced by design (see classify.__init__ docstring and
plan file for the full contract):

  - classify() is pure, local, context-free
  - classify() must not read parent/children, z-path, or any state
  - classify() is total on discriminator_ids (all evaluated)
  - classify() is idempotent (same input → same output)
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Tuple

from cstz.classify.registry import DiscriminatorRegistry


# ---------------------------------------------------------------------------
# Shape witness — local binarized arity and role names
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ShapeWitness:
    """Local structural witness for a binarized node.

    arity ∈ {0, 1, 2}:
      0 → leaf (no children)
      1 → unary node (one child in roles[0])
      2 → binary node (two children in roles[0], roles[1])

    Higher-arity nodes must be binarized before reaching the
    classifier.  Binarization is the walker's responsibility.
    """
    arity: int
    roles: Tuple[str, ...]

    def __post_init__(self) -> None:
        if self.arity not in (0, 1, 2):
            raise ValueError(
                f"arity must be 0, 1, or 2 (binarized); got {self.arity}"
            )
        if len(self.roles) != self.arity:
            raise ValueError(
                f"arity={self.arity} requires {self.arity} roles, "
                f"got {len(self.roles)}: {self.roles!r}"
            )


# ---------------------------------------------------------------------------
# Classified — the per-node projection result
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Classified:
    """A τ-identity signature plus structural witness.

    τ is a bitmask: OR of the one-hot IDs of discriminators that
    fired.  σ is the implicit complement.

    shape carries the binarized arity and role names for use by the
    walker; it does not encode semantics.
    """
    tau: int
    shape: ShapeWitness


# ---------------------------------------------------------------------------
# Classifier — the projection itself
# ---------------------------------------------------------------------------


class Classifier:
    """Projects a subset of registered discriminators onto input nodes.

    Subclasses override shape_of() to provide node-specific
    binarization.  classify() must not be overridden — its purity
    is part of the contract.

    Contract (enforced by design, verified by meta-tests M1-M6):

      - pure: no side effects
      - local: only the single input node is consulted
      - total: all discriminator_ids are evaluated
      - context-free: no parent, children, z-path, or state access
      - idempotent: classify(n) == classify(n) for every n

    These rules prevent Python AST (and any future classifier) from
    leaking scope or traversal info into the identity layer.
    """

    def __init__(
        self,
        registry: DiscriminatorRegistry,
        discriminator_ids: Tuple[int, ...],
    ) -> None:
        # Validate: every listed ID must exist in the registry.
        for d_id in discriminator_ids:
            if d_id not in registry:
                raise ValueError(
                    f"discriminator_id {d_id:#x} not in registry"
                )
        self.registry = registry
        self.discriminator_ids = tuple(discriminator_ids)

    def classify(self, node: Any) -> Classified:
        """Evaluate this classifier's discriminators on a node.

        Returns Classified(tau, shape) where τ is the OR of IDs that
        fired and shape is from shape_of(node).

        Must not be overridden.
        """
        tau = 0
        for d_id in self.discriminator_ids:
            if self.registry.get(d_id).fires(node):
                tau |= d_id
        return Classified(tau=tau, shape=self.shape_of(node))

    def shape_of(self, node: Any) -> ShapeWitness:
        """Return the binarized shape witness for this node type.

        Subclasses MUST override.  Must be pure and local.
        """
        raise NotImplementedError("Classifier subclass must implement shape_of()")
