# M10 extractor cost composition — 2026-10-19

Status: **checked conditional composition; M10 implementation obligations remain OPEN.**
The resumed run compiles the arithmetic ledger and the repaired
`RawExtractorCostComposedV2` composition with Lean 4.32, `-j1 -M4400
-DElab.async=false`, a private object directory and the shared mkdir lock.
See the packet manifest for measured exits, memory, swaps and axiom reports.
The original composition is retained unchanged as failed historical source;
its let-bound `run` was introduced as though it were the acceptance premise.
V2 introduces both binders explicitly. Two missing arithmetic cache dependencies
were compiled locally; the no-model predecessor's retained path supplied the
missing terminal interface. Failed attempts are retained, not certified.

## Target and exact consumer interface

The target is
`AspisR1.RawExtractorCostComposedV2.recorded_extractor_cost_and_failure`
(`lean/RawExtractorCostComposedV2.lean:124`). It uses the *same* decoder,
prover, compiled experiment, fixed tag, original first-read budget `Q`,
decoded-start budget `N`, and acceptance-to-terminal-Checks premise as
`RawChecksAdaptiveFailureNoModel.checked_acceptance_failure_bound_no_model`
(`lean/RawChecksAdaptiveFailureNoModel.lean:34`). Its conclusions are:

- On every accepted evaluation of that experiment, the uniform private-coin
  mean of field operations + recorded-log reads + bit operations is at most
  `Parameters.attemptBudget`.
- Every returned witness satisfies `LiteralProtocol.relation` for that exact
  recorded public statement (transported from the ordinary extractor).
- `δE = 1 / 2^126 ≤ 1 / 2^120`.
- The existing shared-oracle failure mass is at most
  `kappa Q + N * PerAttemptEnvelope.B + δE`.

The collision and decoded-start terms are retained. This does **not** say that
conditioning on arbitrary acceptance leaves failure probability at most δE.
The finite attempt includes internal retries and aborting branches. There is
no new unbounded restart loop or assertion about its expected stopping time.

## Explicit polynomial and units

Write `n` for the stored coefficient-array/word-size bound, `q` for recorded
log size, `L` for list size, `b` for exponent/field representation bits, `c`
for bank calls, `d` for depth, `ell` for RR mass, and `t` for bounded retries.
The parameters `a` and `k` must be fixed uniformly over an input family.

```
C = c * (d*ell+1) * (t+1) * (ell+1)
O = a * (n+q+L+b+1)^k
G = (2*n+1) * (100*n^3+800*n^2+1606*n+5)
D = n * (100*(n+4)*(n+4))
M = n*n + (2*n+1) * (100*(2*n+5)*(2*n+5))
F = C*G + C*D + C*(2*b)*M + O
R = 7*n*q
T = F + R + (F+R+O)*(b+1)^2
```

`T` is an explicit polynomial for fixed `a,k`. `M` is a *proposed* modular
multiply field budget, requiring implementation adequacy below. `R` is a
proposed finite-log bound requiring the actual reconstruction bridge. The
quadratic bit multiplier is likewise a named premise, not an inferred theorem
about machine arithmetic. In particular `q` is not silently identified with
`Q`: the recorded log can include adversary reads.

## Composition and audited predecessor statements

| Component | Actual statement and use |
| --- | --- |
| GCD | `lean/ActualCompPolyGCDCostMirror.lean:43` preserves `Raw.gcdMonic` values; its ledger omits normalization/array overhead. `lean/ActualCompPolyGCDTotalRemainderCost.lean:56` bounds this ledger by `G` for stored arrays of size at most `n`. Directly used by `jobs_charge_le`. |
| Division | `lean/ActualLongDivisionTotalCostV2.lean:105` bounds the actual monic-division mirror by `size * 100*(size+4)^2`, assuming trimmed operands and a nonempty monic divisor. `DivisionJob` carries these premises. Monotonicity gives `D`; directly used. |
| Mod power | `lean/ActualCompPolyPowCost.lean:71` preserves the actual power value; `:79` bounds the modular-multiplication **count** by `2*(log2 exponent+1)`. Directly used; the conversion to field operations is `M` plus the explicit accounting premise. This does not mistake count for field cost. |
| RR | `lean/RRProgramQueryBound.lean:90` bounds actual sequential trace length by depth times mass on all branches. New `RawExtractorCostLedger.rr_trace_to_work` (`:66`) converts this to weighted per-ask work plus fixed work. The actual bank scheduling instantiation is still required. `lean/ProgramQueryCost.lean:9` defines branchwise asks, not expectation. |
| RR abort | `lean/RRConcreteRetryBudget.lean:23` bounds finite-tape abort by `d*ell*(1/2)^t`; `:46` handles two recoveries. `lean/GSConcreteRecoveryBudget.lean:11` handles 31 worst-case calls but explicitly leaves caller count/freshness separate. Do not substitute either for the actual 29+5 byte-bank theorem. |
| Actual byte-bank abort | `lean/GSConcreteByteDecoderBank.lean:41` bounds rejection plus actual bank failure below `2^-126`. Already composed into the imported no-model failure theorem, so this packet does not add the same abort charge twice. |
| Lists | `lean/GSConcreteRuntimeCandidateListLength.lean:19` and `:37` give successful runtime list lengths at most **112**. `lean/GSRuntimeCandidateListLength.lean:9` is a filtering bound conditional on input length at most 112. Neither is a runtime bound. `lean/IncrementalCandidateCost.lean:61` needs decoded **finset cardinality at most 100**, a different invariant. List filtering/merge cost remains in `O`; no 112-to-100 coercion is claimed. |
| Log lookup | `lean/MerkleRecoveryCost.lean:156` gives the three-word digest-comparison count `5505024*Q` under finite-table/path bounds; its model explicitly excludes parsing and byte-comparison work. It is supporting evidence for, not a proof of, `LedgerRefinement.reads` for the executable recorded-log constructor. |
| Output safety | `lean/RawRecordedPublicSpendExtractorReturnedRelation.lean:17` proves every successful ordinary extractor result satisfies the byte relation. Directly used through `CostedExtractor.value`. |

`RawExtractorCostLedger.sum_charge_le` turns bounded occurrence lists into
aggregate natural charges. `jobs_charge_le` composes the three arithmetic
ledgers. `accepted_attempt_cost` (`lean/RawExtractorCostComposedV2.lean:98`)
proves a deterministic bound on every tape, then uses `mean_mono` and
`mean_const` to obtain the finite expectation. This is the counts-to-expectation
bridge; it needs no independence assumption.

## Named hypotheses and remaining implementation obligations

`CostedExtractor.value` refines outputs to
`RawRecordedPublicSpendExtractor.extract run coins`, with no external oracle.
Value equality alone does not certify resource labels. Instantiate a genuine
instrumented implementation and prove `LedgerRefinement` (`:85`):

1. `bounded_jobs`: enumerate all GCD/division/power occurrences (including
   failed retries), prove their counts ≤ C, stored sizes ≤ n and exponent bit
   lengths ≤ b; show total field operations ≤ their weighted ledger + O.
   This must cover scalar normalization, dense interpolation, polynomial
   multiplication, sampling, array work, distance filters, merging and final
   witness checks. Existing partial mirrors do not establish that invariant.
2. `reads`: link executable recorded-log reconstruction to the finite-log cost
   mirror and prove ≤ R actual reads. Parsing/comparison costs also need the
   bit-accounting bridge. Merely counting random root queries does not count
   recorded hash-log reads.
3. `bit_accounting`: prove all bit work ≤ (field operations + log reads + O)
   times `(b+1)^2`, or replace this proposed factor with a proved polynomial.

Also instantiate the unchanged M9 premises (`hQ`, `htag`, `hchecks`, `hN`),
and fix uniform overhead constants/degree. These are explicit hypotheses,
not new axioms. The actual instrumentation/overhead proof is substantial and
cannot be recovered just by summing the supplied component theorems.

Validation is recorded in `evidence/extractor-cost-composed-20261019/manifest.json`.
The focused targets were compiled in dependency order; the successful outputs
were audited through their source `#print axioms` commands. No package-wide or
release-wide frozen replay was run: this packet is a conditional M10 result,
not a formal release. No existing Lean source was edited. C3 must explicitly
supply `CostedExtractor.value`, `LedgerRefinement`, the unchanged M9 premises,
and uniformly fixed overhead constants/degree before claiming extractor
implementation efficiency. This result does not close those obligations.
