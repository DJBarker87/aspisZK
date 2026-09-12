"""Finite linear-mask diagnostics, not a full-view adaptive ZK simulator."""
from __future__ import annotations
from collections import Counter
from itertools import product
from .polynomial import require_prime


def rank(matrix: list[list[int]], p: int) -> int:
    require_prime(p)
    if not matrix:
        return 0
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError('ragged matrix')
    rows = [[x % p for x in row] for row in matrix]; r = 0
    for c in range(width):
        pivot = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        inv = pow(rows[r][c], -1, p); rows[r] = [x*inv % p for x in rows[r]]
        for i in range(r+1, len(rows)):
            factor = rows[i][c]
            rows[i] = [(x-factor*y) % p for x,y in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def witness_shift_hidden(mask_map: list[list[int]], shift: list[int], p: int) -> bool:
    if len(mask_map) != len(shift):
        raise ValueError('output dimension mismatch')
    return rank(mask_map, p) == rank([row+[s] for row,s in zip(mask_map, shift)], p)


def view_histogram(mask_map: list[list[int]], shift: list[int], p: int,
                   *, max_masks: int = 100000) -> Counter:
    require_prime(p)
    if len(mask_map) != len(shift):
        raise ValueError('output dimension mismatch')
    width = len(mask_map[0]) if mask_map else 0
    if any(len(row) != width for row in mask_map):
        raise ValueError('ragged matrix')
    if p**width > max_masks:
        raise ValueError('finite mask enumeration cap')
    return Counter(tuple((sum(a*b for a,b in zip(row,m))+s) % p
                         for row,s in zip(mask_map,shift))
                   for m in product(range(p), repeat=width))
