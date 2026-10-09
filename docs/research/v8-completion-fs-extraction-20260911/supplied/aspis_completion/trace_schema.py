"""Validate instrumented evidence without inventing protocol domain separation.

A trace receipt must contain the literal input bytes supplied to SHA. Semantic
roles, encoded argument boundaries and producer ordinals are evidence metadata;
they do not change the byte stream or prove it matches the Rust implementation.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from .oracle import Event, Prefix, OracleError, validate_events

@dataclass(frozen=True)
class Receipt:
    ordinal: int
    role: str
    parts: tuple[bytes, ...]
    answer: bytes
    depends_on: tuple[int, ...]

    @property
    def raw(self) -> bytes:
        return b''.join(self.parts)


def validate_receipts(receipts: tuple[Receipt, ...], *, check_concrete_sha: bool = False) -> Prefix:
    seen: dict[bytes, bytes] = {}
    events = []
    for i, item in enumerate(receipts):
        if item.ordinal != i:
            raise OracleError('noncontiguous receipt ordinal')
        if any(dep < 0 or dep >= i for dep in item.depends_on):
            raise OracleError('future or self dependency in trace receipt')
        if len(item.answer) != 32:
            raise OracleError('malformed answer')
        if check_concrete_sha and sha256(item.raw).digest() != item.answer:
            raise OracleError('literal input/answer mismatch')
        fresh = item.raw not in seen
        if not fresh and seen[item.raw] != item.answer:
            raise OracleError('inconsistent cached answer')
        seen[item.raw] = item.answer
        events.append(Event(i, item.raw, item.answer, fresh, item.role))
    result = Prefix(tuple(events)); validate_events(result.events)
    return result


def cross_role_aliases(receipts: tuple[Receipt, ...]) -> list[tuple[int, int]]:
    """Alias warning, not automatically a cryptographic attack."""
    first: dict[bytes, Receipt] = {}; out = []
    for item in receipts:
        earlier = first.get(item.raw)
        if earlier is not None and earlier.role != item.role:
            out.append((earlier.ordinal, item.ordinal))
        first.setdefault(item.raw, item)
    return out
