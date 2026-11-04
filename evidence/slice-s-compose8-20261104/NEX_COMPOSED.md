# Slice S composition

Current validated checkpoint: **74/97 rows, 2/7 roots CLOSED**. Target not yet established. Native roots use the NEM ruling-(y) hybrid form: a kernel MODEL theorem plus checked frozen-native caller/child/domain certificates, under the root-owned PacketDomain and PhysicalInterpretation, P6/D188 option-A reclassification, the approved runtime trust rows and RuntimePersistence. No single kernel theorem from Rust source is claimed.

Authority: NEX_VALIDATION.json, NEX_validate.py, immutable NEU baseline and all unchanged predecessor gates. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Headline AspisR1.RPx_Deployed.deployed; frozen3; L154 parameter; D188 narrowed.

RuntimeReturnData under ruling (ab), 2026-11-04, is ADDED runtime trust. No newly closed root uses (ab) at this checkpoint. NEX_ReturnData's model event/order/bound facts are supporting laws, not a proof of platform readback or an op53 Unit erasure. No shipped source changed; no ELF rebuild trigger.

## programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box

Status: OPEN.

No composed native theorem established. Exact outstanding obligations from the accepted handoff:

Need native wrapper to full1880 decoder, exact original Slice, complete error mapping to InvalidAccountData, same boxed return and allocator/frame association. Its decoder/boxed children remain OPEN.

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

## programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement

Status: OPEN.

No composed native theorem established. Exact outstanding obligations from the accepted handoff:

Both constructor children are now composed. L010/L011 prove the full raw/adopted result/state/ordered trace and L012 discharges reached arguments/carriers/ranges. Native common,64-bit guard and finish associations remain OPEN: K120/K126 outer timeouts and K121 solver timeout are excluded; scalar read-set projection is not full native input association.

## crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1

Status: OPEN.

No composed native theorem established. Exact outstanding obligations from the accepted handoff:

Need full320-byte request return/ordered parent composition, actual slice-versus-array magic comparison, payment child/domain join and three zero-binding comparisons. K011..022 prove only the scalar/copy/suffix cuts with relevant comparison replies EXPLICIT arbitrary leaves. Existing NED range/NEQ payment laws are reused; no corrected full extracted reference/native join is established.

## programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer

Status: OPEN.

No composed native theorem established. Exact outstanding obligations from the accepted handoff:

Actual root calls only afterstate decoder/encoder and Variant::S2.tag, not SHA. Need SAME688-byte header, full child Result/Box frame, exact tag byte696 and the frozen library/compiler equality-to-iteration association. L020 and K127/128 cover symbolic induction and one arbitrary equality step only; no whole-buffer bridge.

## programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result

Status: OPEN.

No composed native theorem established. Exact outstanding obligations from the accepted handoff:

Need actual binding validator and792-byte result encoder leaf bridges at derived s, native guard/parent join and an approved coherent effect carrier for the real ordered set_return_data event. L004 retains BindingBridge and EncoderBridge EXPLICITLY; L006 proves the event frame cannot be empty. op53 Unit cannot erase it. K003/004 and K009/010 are supporting cuts only.

Ruling (ab) now resolves the policy/effect-interface question by adding RuntimeReturnData. Exact model bytes, trace position and no later write still require native proof; BindingBridge and EncoderBridge remain explicit, not discharged. (ab) uses: supporting model only; no closed native certificate.

## Newly admitted exact helper

`NEX_Exact.result_state_effects` (L015) reuses NBH_Exact.source. Full statement:

```lean
theorem result_state_effects {State : Type} (n : Usize) (bytes : Slice U8) (state : State) :
    (pool_v1.pair_terminal.exact n bytes,state,([] : List Unit)) =
    (ok (NBH_Exact.result n bytes),state,[])
```

Axioms `[propext, Quot.sound]`. Native coverage is widths8/32, slice length≤33, all input bytes and every return/error, readonly state and empty runtime effects. Actual slice callers must establish these domains at their own call sites. K052..055 execute the frozen helper under KMX and deployed statement features, with matched failing output controls; frozen graph and post-run lock checks pass. The two slice rows TX1:279/TX2:173 are newly CLOSED. No root closure is inferred.
