"""Exact finite decoder/retry distributions; no conditioning away aborts.

This is a sampler-analysis library. It intentionally requires the source's
raw decoder as input instead of guessing Aspis's SHA-to-field mapping.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction
from itertools import product
from typing import Callable, Hashable, Iterable


def retry_distribution(raw_alphabet: Iterable[Hashable], decoder: Callable,
                       attempts: int) -> dict[Hashable | None, Fraction]:
    raw = tuple(raw_alphabet)
    if not raw or len(set(raw)) != len(raw) or attempts < 0:
        raise ValueError('distinct nonempty alphabet and nonnegative attempts required')
    atom = Fraction(1, len(raw))
    one = defaultdict(Fraction)
    for x in raw:
        one[decoder(x)] += atom
    abort = one.get(None, Fraction(0))
    reach = Fraction(1)
    result = defaultdict(Fraction)
    for _ in range(attempts):
        for value, mass in one.items():
            if value is not None:
                result[value] += reach * mass
        reach *= abort
    result[None] = reach
    assert sum(result.values(), Fraction(0)) == 1
    return dict(result)


def ordered_pair_distribution(raw_alphabet: Iterable[Hashable], decoder: Callable,
                              first_attempts: int, second_attempts: int) -> dict:
    raw = tuple(raw_alphabet)
    first = retry_distribution(raw, decoder, first_attempts)
    result = defaultdict(Fraction)
    for x, px in first.items():
        if x is None:
            result[None] += px
            continue
        def second_decode(r):
            y = decoder(r)
            return y if y != x else None
        for y, py in retry_distribution(raw, second_decode, second_attempts).items():
            result[None if y is None else (x, y)] += px * py
    assert sum(result.values(), Fraction(0)) == 1
    return dict(result)


def target_pair_bound(domain_size: int, roots: int) -> Fraction:
    if domain_size < 2 or not 0 <= roots <= domain_size:
        raise ValueError('invalid domain/root cardinality')
    return Fraction(roots * (roots - 1), domain_size * (domain_size - 1))


def assert_uniform_success(dist: dict) -> None:
    masses = [v for k, v in dist.items() if k is not None]
    if masses and any(m != masses[0] for m in masses):
        raise ValueError('successful outcomes are not uniform; decoder multiplicities matter')


def masked31_decoder(word: int) -> int | None:
    """Candidate decoder for testing only; NOT bound to selected source."""
    if not 0 <= word < (1 << 32):
        raise ValueError('not a u32')
    x = word & ((1 << 31) - 1)
    return None if x == (1 << 31) - 1 else x
