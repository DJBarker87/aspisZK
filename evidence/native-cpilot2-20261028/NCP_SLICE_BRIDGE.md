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

## Closed local composition leaves and remaining chain

- DigestDecode: K038 actual proof_for_contract PASS; K039 matched inversion FAIL; K040 verified caller PASS; K041 caller inversion FAIL. K018-K023 supply the full digest-Result shape controls. X002 + L048 establish extract(reference)=cohort decoder for all32-byte inputs, exact Ok/Err payloads, via explicit seven-variant error transport. This is a complete LOCAL leaf bridge; no stage2/headline extraction premise is removed.
- Digest canonicality scanner: K042 actual body with a while invariant PASS; K043 negative FAIL; K044 verified caller PASS; K045 negative FAIL. X003 + NCP_CanonReference.source (L056) connect the byte-identical reference definition to the SAME pair_tree_profile cohort function on all raw digests. NBD_DigestInduction.source is the reused decreasing Lean loop proof.
- exact8/exact32: revised K058/K062 proof_for_contract PASS, K059/K063 negative FAIL, K060/K064 verified caller PASS, K061/K065 negative FAIL. X003 + NCP_ExactReference.source (L054) give the full extracted reference/cohort equality, including length errors, via explicit fifteen-variant transport. Native proof domain is ONLY widths8/32 and input length<=33; NCP_CallerDomains.after_digest/after_index prove the corresponding688-byte model ranges. No N=4 or unbounded native-domain claim.
- Full afterstate validator: K066 TIMEOUT; K067 cancelled queued control. No contract or caller credit. K068/K069 close only one native iteration at arbitrary level<20 and arbitrary prestate, with the already proved canonicality contract; NBH_Frontier.afterstate_loop is its existing model-side induction predecessor. No whole-record contract is inferred.
- Actual digest encoder: K070 compiler ICE for a borrowed invariant dereference in loop_contracts.rs:1125, before verification. It is distinct from the micro-for ICE at394. EncodeRaw/Canonical remain OPEN native. Word-only K024-K027 are diagnostic local contract evidence and are not promoted to a codec bridge.

X003 emitted a map_err external TEMPLATE axiom. That template is NEVER imported. NCP_HelperExtracted.FunsExternal instead abbreviates the coherent cohort's existing extracted generic map_err DEFINITION (L050 inspection, L052 compile); no new axiom or trust item is added. Both helper extractions normalize only their error type identifier to avoid the generated global discriminant instance collision, with inverse byte check. Native/reference function definitions copied into the extraction-only module are byte-identical.

L057 audits all claimed roots, all9 decoder cases, helper references, range domains and the map_err definition. Only propext/Classical.choice/Quot.sound occur (several roots use fewer).

## Remaining Lean-only work and budget stop

After native exhaustion, X004 extracts the byte-identical encode reference. L058/L059 compile its new generated Types/Funs; all three emitted encoder/loop/body axiom prints are standard-only. L060 tests the ONE-ITERATION generic step against the cohort little-endian store law, rather than reducing the whole buffer; it fails with unresolved checked scalar shifts/casts and four-updates versus setSlice. The exact failed source is NCP_EncodeStep_UNACCEPTED.lean.txt, excluded from importable modules and all claims. No admitted theorem or larger heartbeat setting replaces it. Full extract(encode_ref)=cohort encode, and higher-reference extraction/equalities, remain OPEN in addition to the native contract obstacles. The 60 charged Lean slots are exhausted (59 Lean invocations, L036 own dependency preflight).
