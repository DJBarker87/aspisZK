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

## Third immediate finding (70758)

`instDiscriminantPoolV1TreeErrorIsize` differs in BOTH type and value between `AspisR1TerminalDecoder.Types` and `R1Z.BuilderAdmissionExtracted`: carriers are `AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError` and `AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError`; values again use their own `read_discriminant`. Rust origin: `aspis-statement::pool_v1::incremental_merkle::PoolV1TreeError`. The builder source is the EJR-selected RealR1 source above; terminal decoder's frozen source association will be in SOURCES.json. Raw results and receipt: lean-70758/, exit 0, wall 0.587824981 s, peak RSS 1,558,144 KiB, swaps 0. Committed immediately before continuing comparisons. This is a nominal/elaboration disagreement, with semantic agreement still a separate obligation.

## Substantive source-shape disagreement found while tracing 70757

Immediate escalation: the source-associated `verifier.Error` declarations do not even have the same constructor set. FinishRelationCurrent has **8**: Parse, Semantic, Transcript, Relation, Merkle, Query, Checkpoint, Allocation. Privacy ProverCommit has **11**, adding **Rejected, AttemptsExhausted, Entropy**. Exact source spans and whole-file hashes are in VERIFIER-ERROR-SHAPE.json (source hashes 0f2e09a5… and 1cffcca7…). The Stream A source is `docs/research/100bit-spend-path-20261013/lean-candidates/finish-relation-source-candidate-20261019/sources/AspisR1FinishRelationCurrent/Types.lean`; the privacy source is `docs/research/100bit-spend-path-20261013/evidence/real-r1-20261023/dependency-audit/RealR1_AspisR1ProverCommit_Types.lean.host.txt`.

The candidate wrapper crate is `aspis_r1_finish_relation_current` (lib.rs line 846); the privacy extraction uses `aspis_r1_cost_probe::verifier::Error` (crates/aspis-r1-cost-probe/src/verifier.rs lines 20–27). They represent the verifier error origin through different extraction inputs. The candidate generation manifest explicitly says `c8ea8dd49 + UNADOPTED shallow/indexed finish candidate + universal backend elaboration adapter`, and its extraction receipt records Aeneas binary 22232f96de983a1cdd4043a3fe2091b3ea4202fdec7a27789ad2612358fb62ae. This is not evidence of the same frozen source revision or of the ae1 translator.

This source-shape difference is stronger than the already committed nominal mismatch. No total type equivalence can be inferred from a namespace replacement; constructor-preserving equivalence of these two enums is impossible with this constructor count. Any privacy-only bridge must account for the three additional cases and prove that the consumer uses the related subset, or use a different sufficient relation with explicitly proved domain conditions. Never silently drop the variants. Stream A's frozen modules/graph stay unchanged.

Correction to the first source-shape notice: d3bfce818… in extraction/config.json is the Aeneas backend `.olean` hash, not the translator executable hash. The executable pin above comes from extraction/aeneas/receipt.json.tool_pins; the constructor finding is unaffected.

## Complete structural comparison result (native 70760)

Committed immediately on receiving the complete comparison: **112 repeated names are not syntactically identical** in type and/or value. The complete set and every provider/signature class are in nonidentical.json; exact type-difference classes are in TYPE-DISAGREEMENTS.json. CENSUS.json includes all 11,928 names. The comparison covered 126,057 provider pairs: 118,082 exact matches, 7,975 nonmatches, all 7,975 differing in value, 5 differing in type. These include cached equation/proof declarations and duplicated fixture data, not just Rust type extractions. Do not classify every proof-body difference as a Rust type semantics disagreement. The three discriminant conflicts remain the Rust carrier conflicts, including the substantive verifier-error constructor mismatch above. Detailed classification follows without changing any source or object.

The DAG comparison includes binder names, binder info, universe parameters and metadata, with direct equality of canonical node strings (not equality inferred from digests). Positive and negative DAG controls passed; focused raw Expr comparisons independently confirmed all three discriminant failures. Full DAG export 70764 passed in 83.378245256 s at 1,606,032 KiB RSS, 0 swaps. Exact comparisons native 70760 passed in 24.263753180 s at 161,420 KiB RSS, 0 swaps. No theorem or axiom claim is made by either inspection.
