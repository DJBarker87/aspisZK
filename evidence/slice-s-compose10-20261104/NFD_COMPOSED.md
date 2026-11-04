# NFD slice S composition checkpoint

Validated: **94/97 rows,124/129 internal edges,6/7 roots CLOSED**. Baseline NEY86/97,110/129,3/7. Authority: NFD_REQUEST_VALIDATION.json, unchanged inherited NDT/NEX/NEY gates plus the additive NFD validator.47 previously completed mutation/admission tests pass; raw getter tests follow separately. The seven-root target and deployed100-bit per-attempt target are not established.

Frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline AspisR1.RPx_Deployed.deployed; frozen3,L154 parameter,D188 narrowed. The root qualifications are ONLY the root's own PacketDomain and PhysicalInterpretation, approved trust rows/RuntimePersistence and CompositionTrustOptionA. P6/D188 optionA is trust reclassification, not removal. No shipped source changed; no ELF rebuild triggered. RuntimeReturnData(ab) is ADDED trust and has one newly CLOSED native use here: emit_result.

The native claims use ruling(y)'s hybrid form: a kernel MODEL theorem plus a checked frozen native/source/domain/carrier certificate. They are not kernel theorems directly over Rust source text. No callee PacketDomain or PhysicalInterpretation is retained as a root hypothesis in a CLOSED certificate.

## decode_pool_v1_pair_forest_terminal_request_v1 — CLOSED

The frozen root agrees with the installed op23 decoder on every valid immutable root slice, including every header/length/binding rejection, every payment error, and every returned record field. It leaves external state unchanged and emits no external effects. On the reached call it passes exactly the SAME216-byte suffix at offset104 to the selected transfer/withdrawal decoder; transition_kind consumes the SAME byte5. The child domains are all-raw decoder domains, with no assumed canonical input. All three internal edges and18 external/primitive obligations are discharged by the exact source/native/domain certificate. Every child bridge is already CLOSED and is reused.

Native: NFD_K003–030 field checks (K026 excluded in favour of branch-specific K034),K031/032 length partition,K033 shifted-child-argument control. Every credited field has a matched failing control with the exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Full Result/error order, immutable input identity, actual payment-window provenance and component coordinates are checked. NFD_source_checks proves exact frozen native/reference body correspondence after fixed-array/slice signature and pure error-constructor lambda normalization, with mutation controls. NFD_RequestProjection proves complete record extensionality and the exact public carrier roundtrips using inherited public proofs;14 compiled alignment modules bind the native observations to those coordinates.

Full kernel MODEL statement:

```lean
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (runSlice bytes,state,([] : List Unit)) =
    (AspisR1.JHd_RequestNative.decode bytes,state,[])
```

Axioms:[propext,Classical.choice,Quot.sound],NFD_L003. Domain/carrier/extensionality/coordinate axioms:NFD_L004–019,all the same standard subset. Exact source snapshots,source hashes,target/argv,revision,exit,wall,RSS,swap and dependency/Aeneas object pins are retained per attempt. No unbound inner named hypothesis. (ab) uses:none.

## decode_public_statement_box — CLOSED

The native root forwards the same live bytes to the now-CLOSED terminal decoder, preserves each child error mapping, and returns the cohort value in the same freshly allocated Box. K054–105 independently observe all26 fields; K106 rejects wrong allocation and K107 rejects a corrupted child reply. The terminal certificate uses K001–052, K053 and the inherited length gate; L005/L006/L009–032 bind all coordinates, and L035 fixes header/kind/payment-window geometry. No inner named hypothesis remains.

Kernel MODEL theorem `NEX_PublicModel.result_state_effects` (NEX_L032):

```lean
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run bytes,state,([] : List Unit)) =
    (AspisS6CurrentCodecInstallation.decode bytes,state,[])
```

#print axioms:[propext, Classical.choice, Quot.sound], pinned in NEX_L032. Coherent installed endpoint is op47. Root qualifications are listed above; (ab) uses:none.


## crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1

Status: CLOSED.

Inherited certificate: `NEM_crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1`. Exact model statement(s), retained unchanged:

```lean
theorem result_state_effects {State : Type} (s : Statement) (state : State) :
    let observed := NEE_ValidatorOracle.run NEM_PaymentReached.pay NEM_LaneReached.lane
      NEM_LateOracle.late s
    (observed.1,state,observed.2) =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       state,(NED_ValidatorTrace.run s).2) := by
  have same := NEE_ReachedRootModel.result_and_effects NEM_PaymentReached.pay
    NEM_LaneReached.lane NEM_LateOracle.late s
    (fun a reached => NEM_PaymentReached.payment_reached NEM_LaneReached.lane
      NEM_LateOracle.late s a reached)
    (fun d reached => NEM_LaneReached.lane_reached NEM_LateOracle.late s d reached)
    (fun a out reached => NEM_LateOracle.late_reached s a out reached)
  rw [same]

```

Axioms: standard subset of `[propext, Classical.choice, Quot.sound]`, pinned in `evidence/slice-s-compose5-20261102/NEM_L018/receipt.json`.

Native/domain receipts and all explicit root qualifications remain in the pinned inherited certificate. No inner bridge was re-proved or removed. (ab) uses: none.



## crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1

Status: CLOSED.

Inherited certificate: `NEQ_crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1`. Exact model statement(s), retained unchanged:

```lean
theorem result_state_effects {State : Type} (s : Statement) (state : State) :
    let observed := run pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      NEM_PaymentReached.pay NEM_LateOracle.late atomic_statement.encode_digest_canonical s
    (observed.1,state,observed.2) =
      (NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s),
       state,(NED_EncoderTrace.run s).2) := by
  dsimp only
  rw [substitution,NED_EncoderTrace.erases]

```

Axioms: standard subset of `[propext, Classical.choice, Quot.sound]`, pinned in `evidence/slice-s-compose6-20261102/NEQ_L007/receipt.json`.

Native/domain receipts and all explicit root qualifications remain in the pinned inherited certificate. No inner bridge was re-proved or removed. (ab) uses: none.



## OPEN roots

emit_result: CLOSED; see its full statement below. K001 timeout remains excluded. Pool readback remains separate.

reconstruct_asq8_statement: CLOSED; see the certificate below.

scan_proof_buffer: same688-byte header/child Result/Box frame, exact byte696 tag use and native equality-iteration association remain OPEN. Existing induction and child model proofs are reused.

## asq8_common — CLOSED member

All fifteen scalar/array field families on unrestricted actual typed Auth/Candidate inputs agree with the cohort common record, preserving raw noncanonical words. NFD_K038–067 provide positive/corrupt-field pairs; K068 rejects returning a different allocation. The exact frozen body and same fresh uniquely owned returned Box are checked under ruling(aa), the existing Allocator item, and option-A reclassification. NEU_ReconstructCore.common_result, NEU_CallDomains.common_packet and NEU_CommonProjections.common_ext are reused; NFD_L020–034 align each native coordinate, standard axioms only. No inner callee hypotheses remain. This closes one member row; reconstruction root integration follows separately.

## reconstruct_asq8_statement — CLOSED root

The frozen native root agrees with installed op52 on every typed Request/Auth/Candidate, including noncanonical words and both ordered rejection guards. On success it passes the same Auth/Candidate to the CLOSED common child and transfers that same allocated common Box and complete selected public record to the CLOSED transfer/withdrawal constructor. It forwards the same child Result/owned Box and ordered validator effects. No external state changes and no inner callee hypotheses remain.

Native prefix K085/086 checks full guard/error classification; K091–108 observe all nine payment field families with corruption controls; K109 rejects a different common allocation; K110 rejects a changed child reply. The child reply-range restriction (Ok or InvalidInstructionData) is DERIVED by NEU_CallDomains.transfer_reply_range/withdrawal_reply_range and the CLOSED constructor certificates. It is not a root precondition.

Full kernel MODEL statement, reused unchanged from NEU_L011:
```lean
theorem result_state_effects {State : Type} (request : Request) (a : Auth)
    (c : Candidate) (state : State) :
    run request a c state =
    (AspisR1.JHf_ReconstructionSlot.source request a c,state,
      NEU_ReconstructCore.trace (toRequest request) (toAuthenticatedAsq8Accounts a)
        (toPoolV1PairVerifiedAfterstateV1 c))
```

Axioms: [propext, Classical.choice, Quot.sound], NEU_L011, with raw model and reached-domain/carrier/range theorems in NEU_L010/L012. Root qualifications: its own PacketDomain/PhysicalInterpretation, RuntimePersistence, approved trust inventory and CompositionTrustOptionA. No (ab) use. NFD_RECONSTRUCT_TESTS.log records38 passing tests.

## emit_result — CLOSED root

The frozen native emitter constructs exactly the cohort result from every typed statement, passes the same statement/result to the binding validator, passes that SAME result to the encoder, maps every child error in order, checks the complete returned buffer length/magic, and emits exactly one ordered setReturnData event carrying all792 returned bytes on the successful branch. Other branches emit no return-data event. The external state follows the approved runtime return-data model, not an empty Unit effect.

Native K111–126 cover every result coordinate with failing controls. K087–090 prove the full owned encoder reply/guard/send continuation with failing byte, ordering and argument controls. NFD_L035 proves complete output record extensionality and all eight coordinate alignments (standard three axioms). Every internal edge, including conservative method targets, is covered; no target is silently pruned. Reached encoder domain is DERIVED by NEY_EmitComposed.reached_encoder on the same binding success, with binding validator/result encoder already CLOSED.

Full kernel MODEL statement (NEY_L041, reused unchanged):
```lean
theorem result_state_effects {A E : Type}
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) :
    run validate_pool_v1_pair_forest_terminal_result_against_statement_v1 encode
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s =
    AspisR1.JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s
```

Axioms: [propext, Classical.choice, Quot.sound]. Only root qualifications and approved trust remain, plus RuntimeReturnData under(ab), explicitly ADDED trust with one new CLOSED native use. Option A is reclassification. This does not prove the separate Pool immediate readback/program-id check. Nine additional emitter mutations pass in NFD_EMIT_TESTS.log.

## Raw getters — CLOSED members

WideExact::to_limbs now covers EVERY raw eight-u32 carrier, without canonicality. K127/128 use a safe actual-type raw constructor; NFD_RawCarriers.raw_roundtrip proves its surjectivity and limbs_result_state_effects binds the complete ordered array, state and empty effects. This resolves the NEY canonical-only finding. Variant::tag covers all three constructors, K129/130 and NFD_RawCarriers.tag_roundtrip/tag_result_state_effects. NFD_L036 audits all four theorems; axioms empty or the standard three. These four inventory rows are CLOSED.
