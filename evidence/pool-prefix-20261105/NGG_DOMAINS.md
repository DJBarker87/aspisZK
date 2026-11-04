# Exact open domains

B1: For each admitted native execution of the frozen process, each logged child
argument is the very source argument at that cut; account records include keys,
owners, flags, lamports, data bytes, borrow prestate and live authority. The
child's PacketDomain must hold there. Its full Result and mutation range,
including rejection prefixes, are interpreted by its CLOSED child bridge.

B2: Let request be the value returned by decode_terminal_request_box_v1 on
instruction_data[..instruction_data.len()-4] in that execution. Establish the
payment-child PacketDomain for request.public, master/checkpoint/lane decoder
domains for the actual accounts[0..3], and layout indices for those accounts.
Selected registry accounts are accounts[layout.registry_start..+2]; selected
verifier is accounts[layout.verifier_index]; proof is accounts[layout.proof_index];
verifier checkpoint is the mapped layout.verifier_checkpoint_index. Establish
that the SAME seven meta keys are [proof,master,forest_checkpoint,lane,registry,
entry,verifier_checkpoint] and all are readonly nonsigners at that CPI.

B3: THAT CPI's instruction.program_id = the authenticated selected verifier;
instruction.data = the 320 bytes encoded from THAT request. Verify
pool_route::admitted(instruction.data), then preserve the exact account and
request windows into verifier admission. Immediately after CPI success the Pool
reads nonempty ASR8, length 792, with no intervening CPI; use only the adopted
nonempty RuntimeReturnData row (1..1024).

D: For THAT returned statement s, prove the complete explicit predicates
validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()),
validate (ResultAdmission.value s) = ok (.Ok ()), and
lane (ResultAdmission.value s) = ok (.Ok image), where validate and lane are
THE frozen consumer operations on the admitted Pool state. Instantiate
NFR_ModelJoin.same_emitted_settlement with that s, selected program and context,
and NFV's read/helper cuts at that same live allocation/borrow context.
These are OPEN obligations; none is assumed as a bundled equality or wrapper.

Final qualification:NGG_RequestLength proves the model payload lengths, not the actual Pool decoder's admitted byte predicate. NGG_PaymentWindows proves point domains on an already320-byte payment; it does not derive each native payment-child PacketDomain. NGG_MarkerZero supplies list value/count/early-abort induction and an Aeneas byte-equality reference law; no full extracted marker body or actual Iterator::all step association is proved. All production pre-states, child Results and modifies-set obligations in NGG_REMAINING.md remain OPEN. The runtime CPI proposal is pending/unused. The combined headline target fails duplicate GuardBody ownership; the local raw audit cannot discharge that coherence obligation.
