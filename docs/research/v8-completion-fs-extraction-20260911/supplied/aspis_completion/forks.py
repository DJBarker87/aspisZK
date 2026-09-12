"""Replay collector with explicit total work and coherent-prefix grouping.

No useful-fork probability is assumed. Refusing/censored/incoherent branches
are retained in the result instead of disappearing from a success denominator.
"""
from __future__ import annotations
from dataclasses import dataclass
from .oracle import Prefix

@dataclass(frozen=True)
class ForkReceipt:
    branch: int
    prefix: Prefix
    replay_calls: int
    fresh_calls: int
    status: str
    payload: bytes | None

@dataclass(frozen=True)
class Collection:
    receipts: tuple[ForkReceipt, ...]
    usable: tuple[ForkReceipt, ...]
    total_replay_calls: int
    total_fresh_calls: int
    enough: bool


def collect(receipts: tuple[ForkReceipt, ...], target_prefix: Prefix,
            required: int, max_work: int) -> Collection:
    if required < 1 or max_work < 0:
        raise ValueError('bad collector budget')
    if len({r.branch for r in receipts}) != len(receipts):
        raise ValueError('reused branch identity')
    work = fresh = 0; usable = []
    for r in receipts:
        if min(r.replay_calls, r.fresh_calls) < 0 or r.fresh_calls > r.replay_calls:
            raise ValueError('invalid branch resource accounting')
        work += r.replay_calls; fresh += r.fresh_calls
        if r.status == 'USEFUL' and r.payload is not None and r.prefix == target_prefix:
            usable.append(r)
    if work > max_work:
        raise ValueError('total extractor replay budget exceeded')
    return Collection(receipts, tuple(usable), work, fresh, len(usable) >= required)
