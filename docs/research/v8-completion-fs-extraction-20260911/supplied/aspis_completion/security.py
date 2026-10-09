"""Exact classical-ROM accounting with fail-closed unknown terms.

No default global security claim. In particular, a per-prefix residual term
cannot be applied after unrestricted Fiat--Shamir retries without a proved
source coupling/trial-accounting theorem.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import log2
from typing import Iterable

P = (1 << 31)-1
K = P**4
N = K-P**2
PAIR_DEGREE = 90407376
PAIR_BOUND = Fraction(PAIR_DEGREE*(PAIR_DEGREE-1), N*(N-1))
# Conservative rational ceiling for the *reported conditional residual*.
# It is not an independent reconstruction of integratedBudget.
REPORTED_RESIDUAL_CEILING = Fraction(493081653, 10**40)


def bits(bound: Fraction) -> float:
    if bound <= 0:
        return float('inf') if bound == 0 else float('nan')
    return log2(bound.denominator)-log2(bound.numerator)


def collision_bound(fresh_queries: int, digest_bits: int = 208) -> Fraction:
    if fresh_queries < 0 or digest_bits < 1:
        raise ValueError('invalid collision budget')
    return min(Fraction(1), Fraction(fresh_queries*(fresh_queries-1), 2*(1 << digest_bits)))


def target_bound(fresh_queries: int, fixed_targets: int, digest_bits: int = 208) -> Fraction:
    if min(fresh_queries, fixed_targets) < 0 or digest_bits < 1:
        raise ValueError('invalid target budget')
    return min(Fraction(1), Fraction(fresh_queries*fixed_targets, 1 << digest_bits))


def retry_union(per_trial: Fraction, trials: int) -> Fraction:
    if trials < 0 or per_trial < 0:
        raise ValueError('invalid trial budget')
    return min(Fraction(1), trials*per_trial)

@dataclass(frozen=True)
class Term:
    name: str
    bound: Fraction | None
    theorem: str | None
    source_binding: str | None
    scope: str


def certificate(terms: Iterable[Term], *, target_bits: int = 100,
                partition_theorem: str | None = None,
                extracted_witness_theorem: str | None = None) -> dict:
    terms = tuple(terms)
    if not terms or len({t.name for t in terms}) != len(terms):
        raise ValueError('nonempty uniquely named term ledger required')
    unknown = [t.name for t in terms if t.bound is None or not t.theorem or not t.source_binding]
    if partition_theorem is None:
        unknown.append('exhaustive accepted-failure partition')
    if extracted_witness_theorem is None:
        unknown.append('resource-bounded checked payment extraction')
    for term in terms:
        if term.bound is not None and not 0 <= term.bound <= 1:
            raise ValueError('term is not a probability upper bound')
    known = sum((t.bound for t in terms if t.bound is not None), Fraction(0))
    return {
        'status': 'BLOCKED' if unknown else ('NUMERIC_PASS_PENDING_PROOF_REVIEW'
                   if known <= Fraction(1, 1 << target_bits) else 'NUMERIC_FAIL'),
        'known_sum': str(known), 'known_sum_bits': bits(known),
        'unclosed_obligations': unknown,
        'warning': 'Theorem names are audit references, not machine-checked evidence.'
    }


def diagnostic_report() -> dict:
    return {
        'scope': 'arithmetic diagnostics only; no global security theorem',
        'pair_bound': str(PAIR_BOUND), 'pair_bits': bits(PAIR_BOUND),
        'reported_residual_ceiling': str(REPORTED_RESIDUAL_CEILING),
        'reported_residual_ceiling_bits': bits(REPORTED_RESIDUAL_CEILING),
        'conditional_prefix_retries': [
            {'trials': q, 'union_ceiling_bits': bits(retry_union(REPORTED_RESIDUAL_CEILING, q))}
            for q in (1, 2, 16, 256, 65536)],
        'merkle_collision_examples': [
            {'fresh_queries': 1 << exponent,
             'bound_bits': bits(collision_bound(1 << exponent))}
            for exponent in (20, 32, 48, 54, 64)],
        'global_status': 'BLOCKED: actual FS coupling, trial budget and remaining terms unproved'
    }
