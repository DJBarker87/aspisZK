# NCP slice obligations

U02 digest canonical/raw encode and decode OPEN. U03 four codecs retain exact named digest conditions. U05 ASF8 validator and encoder additionally retain TransferEncode and WithdrawalEncode. No conditions discharged yet.

Kani contracts refer to safe Rust references; extraction/reference-to-cohort equality must be proved separately. No XRn join. No changed trust assumptions or security statement.

## Checked model discharge

NCP_ModelDischarge compiles in L027 after 26 unchanged private dependency builds. digest_source/decode_source/transfer_source/withdrawal_source establish exact source-cohort equations for explicit model references; u03 and u05 instantiate NBN_U03.conditional/NBN_U05.conditional without lower-codec hypotheses. All printed roots have standard axioms only. These are MODEL laws: the definitions in this file are not asserted to be extracted Rust references. Native contracts and extract(f_ref) correspondence remain separate OPEN obligations. This does not promote the NBU native CLOSED-CONDITIONAL rows.

K013 proves the actual frozen digest decoder contract against NCP_ref_decode; K014 is its matched failing inversion. K015 fails code generation for stub_verified because Result<[M31;8],AtomicStatementError> lacks Arbitrary. An exact scratch-only Arbitrary implementation is the next independent repair; there is no justification for replacing the returned carrier.
