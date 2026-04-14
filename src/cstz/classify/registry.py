"""DiscriminatorRegistry — the global semantic vocabulary.

A discriminator denotes a semantic distinction, not a classifier
feature.  Each discriminator has global identity: a stable one-hot
bitvector ID, a human-readable name, a semantic contract (doc), a
pure local predicate, and a version.

Stability invariant: once registered, a discriminator's *meaning*
may not change.  New semantics require new discriminators, never
mutation.  τ-vectors are identities; z-path equivalence depends
on semantic immutability.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Dict, List


@dataclass(frozen=True)
class Discriminator:
    """A semantic atom: one distinction with a stable global ID.

    Attributes:
        id:      One-hot bitmask (1 << k for the k-th registered).
                 Stable across processes given a fixed registration
                 order.
        name:    Human-readable identifier, unique within a registry.
        doc:     Semantic contract — what this discriminator means.
        fires:   Pure local predicate.  Must be total and
                 context-free; must not access global state, parent
                 or child nodes, or any mutable context.
        version: Semantic version.  Bump when the discriminator's
                 intended meaning changes (which should be rare —
                 prefer registering a new discriminator).
    """
    id: int
    name: str
    doc: str
    fires: Callable[[Any], bool]
    version: int = 1


class DiscriminatorRegistry:
    """The global vocabulary of semantic discriminators.

    A registry assigns one-hot bitvector IDs (1 << k) to
    discriminators in registration order.  All classifiers sharing
    a registry can compare τ-signatures directly.

    Discriminator names must be unique per registry; re-registering
    a name is forbidden (stability invariant).
    """

    def __init__(self) -> None:
        self._by_id: Dict[int, Discriminator] = {}
        self._by_name: Dict[str, Discriminator] = {}

    def register(
        self,
        name: str,
        fires: Callable[[Any], bool],
        doc: str = "",
        version: int = 1,
    ) -> int:
        """Register a new discriminator; return its one-hot ID.

        Raises ValueError if `name` is already registered.
        """
        if name in self._by_name:
            raise ValueError(
                f"Discriminator {name!r} already registered "
                f"(stability invariant: names are write-once)"
            )
        d_id = 1 << len(self._by_id)
        disc = Discriminator(id=d_id, name=name, doc=doc, fires=fires,
                              version=version)
        self._by_id[d_id] = disc
        self._by_name[name] = disc
        return d_id

    def get(self, d_id: int) -> Discriminator:
        """Look up a discriminator by its one-hot ID."""
        return self._by_id[d_id]

    def get_by_name(self, name: str) -> Discriminator:
        """Look up a discriminator by its name."""
        return self._by_name[name]

    def all(self) -> List[Discriminator]:
        """All registered discriminators, in registration order."""
        return list(self._by_id.values())

    def __contains__(self, d_id: object) -> bool:
        return d_id in self._by_id

    def __len__(self) -> int:
        return len(self._by_id)
