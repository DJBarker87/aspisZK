# Immediate D530 disagreement notice

Found by inspection 70756, before continuing the census. Exact raw elaborated Expr types and values differ for:

`instDiscriminantPoolV1PaymentStatementFormatErrorIsize`

| Provider module | Frozen source file |
|---|---|
| `R1Z.BuilderAdmissionExtracted` | `docs/research/100bit-spend-path-20261013/evidence/real-r1-20261023/dependency-audit/RealR1_R1Z_BuilderAdmissionExtracted.lean.host.txt` |
| `AspisR1WithdrawalValidation.Types` | `evidence/replay-dry3-20261026/RPz2_recovered/AspisR1WithdrawalValidation/Types.lean` |

The first type is `Aeneas.Std.Discriminant AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError Aeneas.Std.Isize`; the second substitutes the DIFFERENT nominal inductive `AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError`. Each value is `Discriminant.mk` for its own carrier and its own `read_discriminant` constant. Thus both type_equal and value_equal are false; level parameters agree.

Rust origin: `aspis-statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError`. The withdrawal wrapper crate calls this `aspis_withdrawal_validation_extract::pool_v1::payment_relation::PoolV1PaymentStatementFormatError`. This establishes a nominal/elaboration disagreement, not yet a different constructor layout, discriminant mapping or Rust semantics. Identical-looking constructor source does not make independently declared inductives definitionally equal.

Raw comparison and exact receipt: `lean-70756/{stdout.log,receipt.json,time.log}`. Exit 0, wall 1.521486384 s, peak RSS 1,543,188 KiB, swaps 0; 6G/8G/swap-0 scope; Lean -M7000. Object hashes and source resolution are pinned in `verified.json`, `preflight.tsv`, and `extraction-provenance-initial.json`. No theorem added; axioms query N/A (raw inspection).

D530 consequence: the existing two carriers cannot be transported by a definitional-identity claim. Preserve Stream A's complete soundness import graph and objects. Privacy must adopt its shared declarations, with a proved equivalence for any retained distinct carrier, before a composed consumer can claim transport. Merely renaming this generated instance would hide the composition problem and is not recommended.

## Second immediate finding (70757)

`instDiscriminantErrorIsize` differs in BOTH type and value between `AspisR1FinishRelationCurrent.Types` and `AspisR1ProverCommit.Types`: the carriers are respectively `AspisR1FinishRelationCurrent.verifier.Error` and `AspisR1ProverCommit.verifier.Error`, and each value names its own `read_discriminant`. This is another nominal disagreement for a Rust verifier error type; exact crate/source association is being traced and will be supplied by the completed census. The frozen source-provider mapping will be in SOURCES.json. Raw results and receipt: lean-70757/, exit 0, wall 0.683140365 s, peak RSS 1,557,556 KiB, swaps 0. Committed immediately before continuing comparisons. No semantic inequality or definitional transport is claimed.
