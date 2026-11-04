# NFD slice S composition checkpoint

Validated: **87/97 rows,113/129 internal edges,4/7 roots CLOSED**. Baseline NEY86/97,110/129,3/7. Authority: NFD_REQUEST_VALIDATION.json, unchanged inherited NDT/NEX/NEY gates plus the additive NFD validator.19 mutation/admission tests pass. The seven-root target and deployed100-bit per-attempt target are not established.

Frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline AspisR1.RPx_Deployed.deployed; frozen3,L154 parameter,D188 narrowed. The root qualifications are ONLY the root's own PacketDomain and PhysicalInterpretation, approved trust rows/RuntimePersistence and CompositionTrustOptionA. P6/D188 optionA is trust reclassification, not removal. No shipped source changed; no ELF rebuild triggered. RuntimeReturnData(ab) is ADDED trust but has zero newly CLOSED native uses here.

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

emit_result: the owned792-byte Ok return-to-send continuation remains unbound. NFD_K001 timed out despite a scalar-only oracle log; no controls were submitted after its timeout. The reviewed replacement splits discriminator/move/window/send instead of increasing limits. NEY_EmitComposed.result_state_effects is reused as the MODEL statement, with native emitter bridge still an explicit OPEN obligation. RuntimeReturnData(ab) remains ADDED trust; Pool readback is separate.

reconstruct_asq8_statement: native asq8_common input-value/Box allocation/ownership association and original guard/common/constructor continuation remain OPEN. Existing general model/domain theorems are reused, never treated as native evidence.

scan_proof_buffer: same688-byte header/child Result/Box frame, exact byte696 tag use and native equality-iteration association remain OPEN. Existing induction and child model proofs are reused.
