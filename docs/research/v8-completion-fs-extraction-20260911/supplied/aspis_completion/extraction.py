"""Bounded candidate-validation wrapper; does not assume candidates exist.

Accepted output is backed by an independently supplied deterministic validator.
Completeness, source authentication and permitted candidate production must be
proved separately. This wrapper must never be counted as their proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Generic, Iterable, TypeVar

T = TypeVar('T')
@dataclass(frozen=True)
class ExtractionResult(Generic[T]):
    status: str
    witness: T | None
    checked: int


def first_valid(candidates: Iterable[T], validate: Callable[[T], bool],
                max_candidates: int) -> ExtractionResult[T]:
    if max_candidates < 0:
        raise ValueError('negative candidate budget')
    it = iter(candidates)
    for i in range(max_candidates):
        try:
            candidate = next(it)
        except StopIteration:
            return ExtractionResult('NO_VALID_CANDIDATE', None, i)
        result = validate(candidate)
        if type(result) is not bool:
            raise TypeError('validator must return bool; exceptions are not success')
        if result:
            return ExtractionResult('VALIDATED', candidate, i+1)
    return ExtractionResult('BUDGET_EXHAUSTED', None, max_candidates)

@dataclass(frozen=True)
class TransferAmounts:
    amount_in: int
    recipient: int
    change: int


def amounts_valid(value: TransferAmounts) -> bool:
    """Only the selected positive 30-bit amount slice, not payment validity."""
    limit = 1 << 30
    return all(type(v) is int and 0 <= v < limit
               for v in (value.amount_in, value.recipient, value.change)) and \
        value.recipient > 0 and value.change > 0 and \
        value.amount_in == value.recipient + value.change
