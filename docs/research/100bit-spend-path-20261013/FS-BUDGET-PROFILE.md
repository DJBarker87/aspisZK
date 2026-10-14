# Query-dependent security arithmetic

The existing ledger's largest raw error coefficient is approximately
`2^-105.136475`. This value has no work or grinding credit. The conditional
unified Fiat–Shamir theorem still uses

```
B(Q) = Q * max_row + 3 * Q^2 / 2^256.
```

These are different quantities. Even after all theorem premises are
discharged, the raw coefficient alone would not establish an absolute
failure bound of `2^-100` for arbitrary `Q`.

`fs_budget_profile.py` reads the exact rational rows of `security-ledger.json`
and evaluates this expression with exact rational arithmetic. The JSON pins
both that ledger and `SemanticBudget.lean`. Its scenarios are neither measured
query counts nor a selected adversarial query budget.

| Q | Approximate −log₂ B(Q), for this formula only |
|---:|---:|
| 1 | 105.136475 |
| 35 | 100.007192 |
| 36 | 99.966550 |
| 1,024 | 95.136475 |
| 2²⁰ | 85.136475 |
| 2³² | 73.136475 |

The largest integer `Q` meeting `B(Q) ≤ 2^-100` is exactly 35. The script
checks that inequality and the failure at 36 using rational arithmetic;
positivity of the coefficients makes `B` increasing on nonnegative `Q`.
This is a limitation of the stated bound, not a demonstrated attack or an
impossibility theorem for a stronger reduction.

The current semantic figures also need to be kept distinct. The ledger
retains the conservative coefficient `435200*(1/P^4 + 1/2^256)`.
`SemanticBudget.lean` gives a maximum row coefficient of 217600 and a
25-row sum of 303100 multiplying the same atom. Their approximate strengths
are 105.268681, 106.268681, and 105.790566 bits, respectively. The profile
records all three without replacing the ledger's chosen row or asserting a
new Fiat–Shamir instantiation.

The [source hash-call inventory](QUERY-CALL-INVENTORY.md) records 583 raw
calls on the visible successful two-fold verifier path and a much larger
scoped prover subtotal. Raw calls are not distinct oracle inputs; the
inventory supplies no full-experiment `Q` bound. It must not be substituted
for the theorem's distinct-read hypothesis.

The later native measurement accepted both phases of one saved P3 S2 proof
and observed 583 raw calls over 452 distinct full byte strings. Its evidence
is in `evidence/hash-input-counter-p3-20261014/`. This is one verifier run,
not an adversarial full-experiment upper bound. For scale, substituting 452
into the conditional expression gives about 96.316296 bits; this does not
turn a run measurement into a security theorem. A complete instantiation
must include prover queries and every additional charged event.

`fs_budget_q_sweep.py` varies only the query term for q=22 through 40,
keeping all other ledger rows fixed. At q=23 the semantic row takes over,
so the best coefficient improves from 105.136475 to only 105.268681 bits.
Further queries alone do not improve this maximum. The exact JSON checks
Q scenarios 2^20, 2^32, 2^40, and 2^64; none meets a total 2^-100 bound under
these fixed-row assumptions. This is an arithmetic limitation of that
parameter-only modification, not a protocol impossibility result.

No total protocol failure probability is certified by this arithmetic.
The concrete classifier, knowledge reduction, and protocol/source/privacy
premises remain open, and additional terminal Merkle events are not fully
included in this expression. A final claim must report its coefficient,
query dependence, and all separately charged events together. If the target
is an absolute `2^-100` bound at a specified budget, that complete expression
must meet the target at that budget; no work normalization removes the factor.

Run `python3 docs/research/100bit-spend-path-20261013/fs_budget_profile.py`
to regenerate the profile. This evaluates twelve small arithmetic scenarios;
it performs no proof generation or large field enumeration.
