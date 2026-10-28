# NCP slice obligations

U02 digest canonical/raw encode and decode OPEN. U03 four codecs retain exact named digest conditions. U05 ASF8 validator and encoder additionally retain TransferEncode and WithdrawalEncode. No conditions discharged yet.

Kani contracts refer to safe Rust references; extraction/reference-to-cohort equality must be proved separately. No XRn join. No changed trust assumptions or security statement.

## Checked model discharge

NCP_ModelDischarge compiles in L027 after 26 unchanged private dependency builds. digest_source/decode_source/transfer_source/withdrawal_source establish exact source-cohort equations for explicit model references; u03 and u05 instantiate NBN_U03.conditional/NBN_U05.conditional without lower-codec hypotheses. All printed roots have standard axioms only. These are MODEL laws: the definitions in this file are not asserted to be extracted Rust references. Native contracts and extract(f_ref) correspondence remain separate OPEN obligations. This does not promote the NBU native CLOSED-CONDITIONAL rows.

K013 proves the actual frozen digest decoder contract against NCP_ref_decode; K014 is its matched failing inversion. K015 fails code generation for stub_verified because Result<[M31;8],AtomicStatementError> lacks Arbitrary. An exact scratch-only Arbitrary implementation is the next independent repair; there is no justification for replacing the returned carrier.

## Extracted decoder reference

X001 preserves the first shift/OR reference extraction. X002 extracts the revised safe u32::from_le_bytes reference with Charon cb50ff16 (binary daad69be...) / nightly-2026-06-01 and Aeneas b59d5188-lean432-extended audited source tree 3be6820e (binary c0cf4fcc...). Raw generated sources and full tool/output hashes are in NCP_EXTRACTION2_* and NCP_extracted_v2/. Only the generated error type identifier is normalized to avoid a global discriminant-instance collision (inverse replacement checked).

L048 proves NCP_DecodeReference.reference_model and reference_source on EVERY 32-byte input, including each first-noncanonical error and full raw digest payload. Standard axioms only. Eight rejecting-prefix modules plus the successful case replace the default-heartbeat failure L034; no heartbeat cap increase or unchanged retry. L036 was an own missing-dependency preflight (no Lean), fixed by adding the missing NBN type import. Rejected attempts that printed sorryAx have exit 1 and supply no credit; final accepted sources contain no admission. Native Kani quartet against this exact revised reference remains to be re-established next.

Pinned while-loop abstraction controls K034-K037 behave as expected; for/enumerate controls K032-K033 hit loop_contracts.rs:394 Option::unwrap ICE. Online current documentation https://model-checking.github.io/kani/reference/experimental/loop-contracts.html describes inductive abstraction, but support is determined by these pinned trials, not inferred from current docs.
