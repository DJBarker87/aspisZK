# Fixed-word openings into the same typed terminal recurrence

Status: **source-review ready, not compiled**. New target
`experiments/FixedWordQueryTerminal.lean`, SHA256
`3f1df287a01be1c1660071347f77d1dc95e87871e00b65417b9b49a307975c35`,
six intended audits. Observed source parent:
`125320408ae38060fab9c97391958025d353ce10`. No compiler or cache mutation was
launched. Prior query and typed-terminal checkpoints remain frozen.

## Conditional theorem

`acceptance_fixed` proves the following deterministic equivalence for q22:

```text
fixed total word and earlier quotient/ordinary inputs
  + exact canonical parsing of these 22 records
  + each record opening equals that fixed word at its queried four slots
  + successful ordered inverse constructor
  => typed record-value terminal acceptance
     iff CausalOrderedRelation.accepts for the same fields and challenges.
```

The object `FixedInput` contains the total word, the OOD/chord data, ordinary
functional, analysis reference Q, initial scalar and quarter. Its `before`
constructor uses the SAME chord `b,c` as the query quotient, so deferred image
and chord coefficients cannot silently diverge. None of its fields has a
tau/alpha/query/rho argument. For an actual experiment, however, the caller
still must construct this SAME object before the continuation and quantify
opening equality across all relevant histories. A theorem applied separately
after each query with a newly chosen object would not establish that causality.

`OpeningEquality` is explicit:

```text
fixed.word(childIndex(queryIndex[i],slot))
  = rawCombined(fixed.chord.gamma, records[i], slot).
```

It is neither assumed to follow from canonical parsing nor obtained from the
post-query `observedWord` extension. The new file never calls `observedWord`.
The total word may be arbitrary and non-polynomial. The selected oracle uses
the full stored domain as its corruption set, so no support, image-validity
or successful-recovery premise is hidden in its constructor.

## Exact composition

| New interface | Reused checked theorem |
|---|---|
| `values_source_iff` | `TypedRelationTerminal.first_claim_horner`; pointwise equality gives the original-ordinal `rho^(i+1)` sum |
| `indexed_point` | `SelectedReceivedOracle.point_index` for the actual typed schedule member |
| `received_fixed` | `SelectedPackedQueryBridge.matching_fold`, then `QueriedResidual.success_fold`; two `oracle_folded` applications transport arbitrary reference Q without changing received values |
| `residual_fixed` | Same indexed final256 evaluation minus SAME fixed-word quotient fold |
| `acceptance_fixed` | `TypedRelationTerminal.source_accepts_iff`, using the SAME `Fields` strategy, snapshot, final, queries, rho, and three later alphas |
| `collision_or_acceptance` | Consumes a supplied `collision ∨ OpeningEquality`; adds no collision extraction or probability theorem |

The source-facing `acceptsValues` spells out the record-ordinal plus query
injection, three compact Horner recurrences, ordinary/query dual weights, and
deferred image contribution. The record fold already includes affine
subtraction, checked chord division, signs `(++,+−,−−,−+)`, and alpha0's
four-slot fold. Query weights remain in their later line-domain batch; they
do not undergo chord division or the alpha0 fold again.

`Fields.firstResponse` depends only on tau; `Fields.final` depends on tau and
alpha0 but not future queries/rho; later response functions depend only on
their allowed prefix. Actual canonical response/final buffers can be supplied
through the prior `TypedRelationTerminal.Decoded.fields` constructor. This
new leaf does not claim a particular Rust `Wire` has been translated to those
functions. The ordinal array is never sorted to match authentication paths.
No nonzero alpha0 requirement is introduced.

## Remaining external boundaries

- Construct the earlier fixed total word from the actual commitments, or
  prove an actual collision alternative with its hash-call/resource scope.
- Prove the literal decoder/optimized arithmetic/point lookup and inverse
  buffers implement the mathematical parser and checked inverse constructor.
- Supply the actual ordinary shifted functional, initial scalar, quarter,
  canonical response/final buffers, and chord data from the SAME earlier
  transcript. The typed identity is valid for arbitrary quarter; identifying
  the actual source's `1/4` belongs to that source constructor.
- Preserve the V8 structured transcript order and framing, not a V7 schedule.
- Establish any challenge law, history-uniform source coupling, FS/ROM fork
  conditions, authenticated support or probabilistic bound separately.

The equivalence remains useful without those claims, but it is conditional
terminal algebra, not `verify_parsed success -> full accepted execution`.

## Proposed focused check

Direct imports only:

- `SelectedPackedQueryBridgeV3`: source
  `71d263e01f07515e094b98cc7a21734d73137be7da9e6a2dbd6d655393f9f954`,
  output `84fe18f47a8b6a667ff54d5c30588ef59fa73facb91c8cc81213c5186814f6e0`.
- `TypedRelationTerminalV3`: source
  `05a8ea8a361cbb09fa426287d37f446b3123329e9b7bf46d88dda726ff4be9a3`,
  output `ab7f519f9f4820b81b2479778b828d4bfb551db34a79268f370181779b1b51d8`.

No additional borrowed module or package build is needed. The fourteen old
query dependency pairs remain installed but omitted from prior run manifests;
their separate post-run observation/provenance caveat is not repaired by a
new import. Request one fresh-tag capped Tailscale NUC target only after the
coordinator grants its slot. Source maxRecDepth200/maxHeartbeats200000 and the
usual Lean `-j1 -M9500`, 8/10-GiB, swap0, CPU200% scope remain unchanged.
