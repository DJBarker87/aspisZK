"""Exact prime-field polynomial and Berlekamp--Welch reference decoder.

This is NOT the Aspis circle/QM31 decoder. It is an executable algebra/control
oracle for decoder testing. The deployed field, basis, degree, evaluation-point
and circle/GRS transformation refinements remain explicit integration tasks.
"""
from __future__ import annotations
from functools import lru_cache
from math import isqrt
from typing import Sequence

class DecodeError(ValueError):
    pass

@lru_cache(None)
def require_prime(p: int) -> None:
    if p < 2:
        raise ValueError('field modulus must be prime')
    if p > (1 << 32):
        raise ValueError('reference primality checker deliberately capped at 32 bits')
    if p % 2 == 0:
        if p != 2:
            raise ValueError('composite modulus')
        return
    for d in range(3, isqrt(p)+1, 2):
        if p % d == 0:
            raise ValueError('composite modulus')


def trim(a: Sequence[int], p: int) -> list[int]:
    result = [v % p for v in a]
    while result and result[-1] == 0:
        result.pop()
    return result


def evaluate(a: Sequence[int], x: int, p: int) -> int:
    value = 0
    for c in reversed(a):
        value = (value * x + c) % p
    return value


def multiply(a: Sequence[int], b: Sequence[int], p: int) -> list[int]:
    if not a or not b:
        return []
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = (out[i+j]+x*y) % p
    return trim(out, p)


def divmod_poly(a: Sequence[int], b: Sequence[int], p: int) -> tuple[list[int], list[int]]:
    remainder, divisor = trim(a, p), trim(b, p)
    if not divisor:
        raise ZeroDivisionError('zero polynomial')
    q = [0]*max(0, len(remainder)-len(divisor)+1)
    inverse = pow(divisor[-1], -1, p)
    while remainder and len(remainder) >= len(divisor):
        offset = len(remainder)-len(divisor)
        c = remainder[-1]*inverse % p; q[offset] = c
        for j, d in enumerate(divisor):
            remainder[offset+j] = (remainder[offset+j]-c*d) % p
        while remainder and remainder[-1] == 0:
            remainder.pop()
    return trim(q, p), remainder


def solve_linear(matrix: Sequence[Sequence[int]], rhs: Sequence[int], p: int) -> list[int]:
    """RREF solution with free variables set to zero; inconsistency is explicit."""
    require_prime(p)
    if not matrix or len(matrix) != len(rhs):
        raise ValueError('empty/ragged linear problem')
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError('ragged matrix')
    rows = [[v % p for v in row]+[b % p] for row, b in zip(matrix, rhs)]
    pivots: list[int] = []; rank = 0
    for col in range(width):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][col], -1, p)
        rows[rank] = [x*inv % p for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col]:
                factor = rows[i][col]
                rows[i] = [(x-factor*y) % p for x, y in zip(rows[i], rows[rank])]
        pivots.append(col); rank += 1
        if rank == len(rows):
            break
    if any(not any(row[:width]) and row[-1] for row in rows):
        raise DecodeError('inconsistent interpolation equations')
    result = [0]*width
    for i, col in enumerate(pivots):
        result[col] = rows[i][-1]
    if any(sum(a*x for a, x in zip(row, result)) % p != b % p
           for row, b in zip(matrix, rhs)):
        raise AssertionError('internal linear solver verification failed')
    return result


def berlekamp_welch(xs: Sequence[int], ys: Sequence[int], k: int, t: int, p: int) -> tuple[int, ...]:
    require_prime(p)
    if k < 1 or t < 0 or len(xs) != len(ys) or len(xs) < k+2*t:
        raise DecodeError('need n>=k+2t and matching nonempty samples')
    if len(set(x % p for x in xs)) != len(xs):
        raise DecodeError('evaluation points are not distinct')
    if any(not 0 <= x < p for x in xs) or any(not 0 <= y < p for y in ys):
        raise DecodeError('noncanonical input')
    # Q has degree <k+t; E is monic of degree t.
    # Q(x)-y*sum(e_j*x^j)=y*x^t.
    matrix = []; rhs = []
    for x, y in zip(xs, ys):
        matrix.append([pow(x, j, p) for j in range(k+t)] +
                      [(-y*pow(x, j, p)) % p for j in range(t)])
        rhs.append(y*pow(x, t, p) % p)
    sol = solve_linear(matrix, rhs, p)
    q = sol[:k+t]; locator = sol[k+t:] + [1]
    candidate, remainder = divmod_poly(q, locator, p)
    if remainder or len(candidate) > k:
        raise DecodeError('candidate is not a message polynomial')
    candidate += [0]*(k-len(candidate))
    errors = sum(evaluate(candidate, x, p) != y for x, y in zip(xs, ys))
    if errors > t:
        raise DecodeError('too many inconsistent samples')
    return tuple(candidate)


def decode_columns(xs: Sequence[int], columns: Sequence[Sequence[int]],
                   k: int, t: int, p: int) -> tuple[tuple[int, ...], ...]:
    """All columns share a single corruption-support check; no column union fudge."""
    if not columns:
        raise DecodeError('empty column family')
    recovered = tuple(berlekamp_welch(xs, ys, k, t, p) for ys in columns)
    bad = {i for i, x in enumerate(xs)
           if any(evaluate(poly, x, p) != col[i] for poly, col in zip(recovered, columns))}
    if len(bad) > t:
        raise DecodeError('union of column corruption supports exceeds common budget')
    return recovered
