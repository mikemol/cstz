"""Classifier layer — τ-identity projections over a global discriminator basis.

Architecture (three layers, from semantic atoms to observations):

    Layer 1:  DiscriminatorRegistry (global semantic vocabulary)
    Layer 2:  Classifier            (local projection, returns Classified)
    Layer 3:  Walker + Adapter      (compose τ along z-paths, emit to Patch)

Key invariants:

    τ is identity; σ is implicit
    Discriminator stability (no re-meaning)
    Classifier idempotence (pure, local, context-free)
    Walker monotonicity (no retroactive rewrites)
    Adapter minimality (τ-only, injective, monotone)

Mirrors: the Agda formalization at agda/CSTZ/Framework/ and the
observation protocol at cstz.observe.

Cofibration (STUDY.md §8.3, Python cofiber): classification is runtime
only. The Agda formalization fixes the *algebra* of discriminators
(``agda/CSTZ/Framework/Discriminator.agda``) but does not prescribe how
to obtain discriminators from concrete syntax — that is this module's
job. ``DiscriminatorRegistry``, ``Classified``, ``Walker``, and
``Adapter`` have no Agda counterpart because they map bytes / AST
nodes / tokens to bitmasks, which is an operational concern rather
than a mathematical one.
"""

from cstz.classify.registry import Discriminator, DiscriminatorRegistry
from cstz.classify.base import Classified, ShapeWitness, Classifier
from cstz.classify.walker import zpath, walk, KeyFn, ChildrenFn
from cstz.classify.adapter import emit_patch
from cstz.classify.bytes import morton2

__all__ = [
    "Discriminator", "DiscriminatorRegistry",
    "Classified", "ShapeWitness", "Classifier",
    "zpath", "walk", "KeyFn", "ChildrenFn",
    "emit_patch",
    "morton2",
]
