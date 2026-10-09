"""Instrumented classical lazy oracle and permitted-prefix access.

The answer generator is external. Test RNG answers emulate a finite ROM;
SHA256 answers can check concrete replay but are not evidence of randomness.
Role labels are metadata and are NEVER prepended to the actual hash input.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from typing import Callable, Iterable

class OracleError(ValueError):
    pass
class MissingAnswer(OracleError):
    pass
class BudgetExceeded(OracleError):
    pass

@dataclass(frozen=True)
class Event:
    ordinal: int
    input: bytes
    answer: bytes
    fresh: bool
    role: str

@dataclass(frozen=True)
class Prefix:
    events: tuple[Event, ...]

    def table(self) -> dict[bytes, bytes]:
        validate_events(self.events)
        result: dict[bytes, bytes] = {}
        for event in self.events:
            result[event.input] = event.answer
        return result

    @property
    def calls(self) -> int:
        return len(self.events)

    @property
    def fresh_calls(self) -> int:
        return sum(event.fresh for event in self.events)

    def extends(self, earlier: 'Prefix') -> bool:
        return self.events[:earlier.calls] == earlier.events


def validate_events(events: Iterable[Event], answer_bytes: int = 32) -> None:
    table: dict[bytes, bytes] = {}
    for i, event in enumerate(events):
        if event.ordinal != i or len(event.answer) != answer_bytes:
            raise OracleError('noncontiguous log or malformed digest width')
        present = event.input in table
        if event.fresh != (not present):
            raise OracleError('incorrect fresh/cache flag')
        if present and table[event.input] != event.answer:
            raise OracleError('oracle was reprogrammed at a cached input')
        table[event.input] = event.answer

class LazyOracle:
    def __init__(self, answer: Callable[[bytes], bytes], *, max_fresh: int, max_calls: int):
        if min(max_fresh, max_calls) < 0:
            raise ValueError('negative resource limit')
        self._answer = answer
        self.max_fresh = max_fresh
        self.max_calls = max_calls
        self._table: dict[bytes, bytes] = {}
        self._events: list[Event] = []

    def query(self, raw: bytes, role: str = 'unspecified') -> bytes:
        raw = bytes(raw)
        if len(self._events) >= self.max_calls:
            raise BudgetExceeded('total query-call budget')
        fresh = raw not in self._table
        if fresh:
            if len(self._table) >= self.max_fresh:
                raise BudgetExceeded('fresh query budget')
            value = bytes(self._answer(raw))
            if len(value) != 32:
                raise OracleError('answer generator must return 32 bytes')
            self._table[raw] = value
        value = self._table[raw]
        self._events.append(Event(len(self._events), raw, value, fresh, role))
        return value

    def freeze(self) -> Prefix:
        return Prefix(tuple(self._events))

    @classmethod
    def resume(cls, prefix: Prefix, answer: Callable[[bytes], bytes], *,
               max_fresh: int, max_calls: int) -> 'LazyOracle':
        obj = cls(answer, max_fresh=max_fresh, max_calls=max_calls)
        obj._table = prefix.table()
        obj._events = list(prefix.events)
        if len(obj._table) > max_fresh or len(obj._events) > max_calls:
            raise BudgetExceeded('prefix already exceeds budget')
        return obj

class FrozenAccess:
    """Read-only extraction access: no ability to ask for a missing hash answer."""
    def __init__(self, prefix: Prefix, max_reads: int):
        if max_reads < 0:
            raise ValueError('negative read budget')
        self._table = prefix.table()
        self.max_reads = max_reads
        self.reads = 0

    def lookup(self, raw: bytes) -> bytes:
        if self.reads >= self.max_reads:
            raise BudgetExceeded('extractor read budget')
        self.reads += 1
        if raw not in self._table:
            raise MissingAnswer('input absent from the authorised frozen prefix')
        return self._table[raw]


def phase_prefixes(full: Prefix, early_cut: int, c2_cut: int,
                   lambda_call: int, ood_call: int) -> tuple[Prefix, Prefix]:
    """Check supplied trace cut positions; does not discover the real source cuts."""
    validate_events(full.events)
    if not 0 <= early_cut <= lambda_call < c2_cut <= ood_call < full.calls:
        raise OracleError('wrong C1/lambda/C2/OOD chronological cuts')
    return Prefix(full.events[:early_cut]), Prefix(full.events[:c2_cut])


def digest_collision(events: Iterable[Event], width: int = 26) -> bool:
    if not 1 <= width <= 32:
        raise ValueError('digest width')
    reverse: dict[bytes, bytes] = {}
    for event in events:
        digest = event.answer[:width]
        if digest in reverse and reverse[digest] != event.input:
            return True
        reverse[digest] = event.input
    return False


def concrete_sha256(raw: bytes) -> bytes:
    """Concrete deterministic test oracle, NOT an ideal random oracle."""
    return sha256(raw).digest()
