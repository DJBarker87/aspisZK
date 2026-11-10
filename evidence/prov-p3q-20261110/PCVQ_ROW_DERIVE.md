# Draft row text: ReviewedTranscription-FieldDerives (Clone, PartialEq on M31, CM31, QM31, WideExact)

Draft only; not added to any document. Job PCVQ_, 2026-11-10. Target not yet established.

Statement. The derived `Clone` and `PartialEq` impls on `M31` (crates/aspis-core/src/field.rs:22), `CM31` (field.rs:254), `QM31` (field.rs:431) and `WideExact` (crates/aspis-core/src/field/wide_exact.rs:27), frozen revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, have the semantics of field-wise clone and field-wise equality in declaration order. The Lean transcription `PCVQ_DeriveRef` (evidence/prov-p3q-20261110/PRVEq_DeriveRef_q1.lean, scope PCVQ_L025, exit 0, axioms propext/Quot.sound only) states `m31_clone`, `cm31_clone`, `qm31_clone`, `we_clone` and the matching `*_eq` functions at those lines, and proves `deployed_qm31_clone`: the clone slot (`fun x => ok x`) used by the deployed resume (yDep, NIL_FreshOps.resume) equals `qm31_clone`; `qm31_clone_id`, `we_clone_id`: the transcriptions are the identity; `qm31_eq_iff`, `we_eq_iff`: the field-wise equality is equality.

Members. One row for the pair: Clone and PartialEq on the four types above. Carriers are the gate types (M31 is the gate's U32).

Class. ReviewedTranscription. What is machine-checked is that the deployed slot equals the transcription; that the transcription matches the derive is a reviewed item (line-by-line against the quoted derives). Not a Charon extraction of the derived impls.

Removal condition. A Charon root that extracts the derived `Clone::clone` and `PartialEq::eq` impls for these four types at the matching configuration, with a proved equality between that emission and `qm31_clone`/`we_clone`/`qm31_eq`/`we_eq` (and hence the deployed slot).
