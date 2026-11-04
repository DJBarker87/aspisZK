# Slice S composition checkpoint

**86/97 rows, 110/129 internal edges, 3/7 roots CLOSED. The seven-root target is not established.** Baseline NEX:82/97,93/129,2/7. Authority: NEY_ENCODER_VALIDATION.json, NEY_LEDGER_DELTA.json, NEY_CHECKED_ROWS.json and the unchanged inherited validator chain. All 24 mutation/validation tests pass (NEY_ENCODER_TESTS.log).

Frozen native revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline AspisR1.RPx_Deployed.deployed, frozen3, L154 parameter, D188 narrowed. No shipped file changed. ELF rebuild was not triggered. Native composition is ruling(y)'s hybrid: a kernel MODEL theorem plus checked actual frozen caller/child/domain certificates, never a claimed kernel theorem directly over Rust source. P6/D188 optionA is trust reclassification. Approved NDT trust rows and RuntimePersistence remain unchanged.

Every CLOSED root's ONLY qualifications are its own PacketDomain and PhysicalInterpretation, approved trust rows/RuntimePersistence and CompositionTrustOptionA. No callee PacketDomain/PhysicalInterpretation is retained as a root hypothesis. Same inputs, canonical carriers, prestate, complete Result including errors and ordered effects are checked at each actual callsite. Certificate edge classifications are in NEY_LEDGER_DELTA.json; all129 edges, including conservative alternatives, remain listed in NEY_EDGES.json.

RuntimeReturnData under(ab) is ADDED runtime trust, used only by supporting emission MODEL facts here. **New CLOSED native(ab) uses:0.** This does not prove runtime readback. No new function-pointer or writable-static pass is credited or quarantined; inherited quarantines remain unchanged.

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


## Newly CLOSED non-root members

The terminal statement decoder, binding validator and result encoder are newly CLOSED. Binding K109/K110 preserves both child Results/arguments/order at the derived record; L004/L007/L040 derive the reached same-statement domain. Encoder K111–128 covers nine disjoint windows, with matched corruption controls and exact child arguments/Results. L002/L008/L037–040 join the actual KMX writes into the cohort792-byte stores and payload. This closes4 additional rows and17 additional edges; no OPEN emitter is promoted from its child closures.

## OPEN root obligations

No complete native composed theorem is established for the following roots. Missing native bridges are explicit obligations, never hidden premises or a self-assumed root bridge.

### decode_pool_v1_pair_forest_terminal_request_v1 — OPEN

K133/K134 close the isolated actual four-byte slice/array magic comparison and K135/K136 the isolated zero32 comparison, with failing controls. Still need the full 320-byte request record field/window join, exact payment child slice/domain/Result/error path and original parent call/order/frame association; isolated comparison checks are SUPPORT ONLY.

Explicit unbound call-domain obligations:

- `call-domain:crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind`
- `call-domain:crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1->crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1`
- `call-domain:crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1->crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1`
- `external:TX2:163:3`
- `external:TX2:163:4`
- `external:TX2:163:5`
- `external:TX2:163:6`
- `external:TX2:163:7`
- `external:TX2:163:8`
- `external:TX2:163:9`
- `external:TX2:163:10`
- `external:TX2:163:11`
- `external:TX2:163:12`
- `external:TX2:163:13`
- `external:TX2:163:14`
- `external:TX2:163:15`
- `external:TX2:163:16`
- `external:TX2:163:17`
- `external:TX2:163:18`
- `external:TX2:163:19`
- `external:TX2:163:20`

### emit_result — OPEN

Binding validator and nine-window result encoder are now CLOSED members. NEY_EmitComposed.result_state_effects discharges their MODEL bridges and derives the reached same-statement encoder domain. The original native emitter still lacks an efficient split certificate for the owned 792-byte Ok return-to-send continuation, same payload/order/guard and exact child arguments. K129–132 timed out and are excluded. Do not assume the root bridge. RuntimeReturnData under (ab) is ADDED trust, supporting model only; zero new CLOSED native uses.

Explicit unbound call-domain obligations:

- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result->crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1`
- `external:TX2:219:8`
- `external:TX2:219:9`
- `external:TX2:219:10`
- `external:TX2:219:11`
- `external:TX2:219:12`
- `external:TX2:219:13`

### reconstruct_asq8_statement — OPEN

Constructor children and the full raw/adopted model/domain laws are inherited. Native common association remains OPEN (K137 timeout); native 64-bit guard and common/constructor continuation owned-carrier/Result/order frame also remain unbound. Four isolated RHS checks do not close the fifteen-field common or the original root.

Explicit unbound call-domain obligations:

- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement->programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement->programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement->programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box`
- `external:TX2:224:3`
- `external:TX2:224:4`
- `external:TX2:224:5`
- `external:TX2:224:6`

### scan_proof_buffer — OPEN

Need the SAME 688-byte header and child Result/Box frame, exact byte696 tag association, and native compiler/library equality-to-iteration association. K150/K146 tag observations do not identify this root callsite/carrier. Existing equality-step/Lean induction and afterstate child bridges are reused; no whole-buffer replay is proposed.

Explicit unbound call-domain obligations:

- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer->crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer->crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1`
- `call-domain:programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer->crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1`
- `external:TX2:226:3`
- `external:TX2:226:4`
- `external:TX2:226:5`
- `external:TX2:226:6`
- `external:TX2:226:7`
- `external:TX2:226:8`
- `external:TX2:226:9`
- `external:TX2:226:10`
- `external:TX2:226:11`
- `external:TX2:226:12`

## Supporting emission MODEL theorem

`NEY_EmitComposed.result_state_effects` has no free BindingBridge/EncoderBridge hypothesis. This completes the Lean continuation; it does not replace the missing actual native emitter certificate. Full statement:

```lean
theorem result_state_effects {A E : Type}
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) :
    run validate_pool_v1_pair_forest_terminal_result_against_statement_v1 encode
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s =
    AspisR1.JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s
```

#print axioms:[propext, Classical.choice, Quot.sound], NEY_L041 and aggregate NEY_L042. The reached encoder domain is derived from successful binding on the SAME statement, never an extra root precondition. RuntimeReturnData remains an explicit ADDED trust item for a future native(ab) closure.

## Audit and limits

NEY_L042 imports36 accepted modules and prints axioms for50 theorem references. Exit0,wall2.200257s,peak5312644KiB,swap0; revision856586302a119162e4181e314d8c6c3ba857a243 with dirty source snapshots pinned. All axioms are a subset of[propext,Classical.choice,Quot.sound]. Exact targets, status,time,RSS,swap,revision,source hashes and axioms for every run are in NEY_SECTION6_RECEIPTS.json and individual receipts. Failed elaborations/compilations/timeouts are retained and excluded.

Budget150/150 Kani,42/60 Lean,192/210 combined(91.43%). NEY_STOP_AUDIT.json lists all eight remaining members and why further Lean-only work cannot supply the missing native evidence. K129–132 and K137 timed out, with no credit. The controller submitted three emission controls before review of the initial timeout; this sequencing violation is recorded in NEY_TIMEOUT_FINDING.json. No further unchanged timeout shape was run after review; caps/timeouts were never raised.

K148/K149's canonical-only getter probe is narrower than NBG's all-raw carrier domain: it is a finding and earns no composed credit. K150/K146's all-variant tag observation and K133–136's request comparisons are supporting checks, not complete selected domain/physical/native contract certificates. K138–145 are explicitly source-isolated RHS checks, not an original whole-aggregate proof. No multiplication was checked in Kani.
