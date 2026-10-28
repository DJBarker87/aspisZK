# NBG U02 atomic digest and payment codecs — OPEN

Eight local members CLOSED; exactly eight enclosing codec members OPEN below.
Frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; coherent SInt2 selection, source/body
pins and all retained boundaries as NBG_U01_BRIDGE.md. No headline premise removed.

| Member | Status | Evidence / domain |
|---|---|---|
| `decode_digest_canonical` | OPEN | Native/model closure incomplete; exact next obligation below. |
| `encode_digest_canonical` | OPEN | Native/model closure incomplete; exact next obligation below. |
| `unwrap_fixed_slice` | CLOSED local | K018; NBG_Atomic.unwrap_ok/unwrap_err; generic Copy success payload; native representative u64 plus uniform source match; callers prove fixed-width Ok conversion |
| `decode_common` | OPEN | Native/model closure incomplete; exact next obligation below. |
| `decode_pool_v1_private_transfer_public_v1` | OPEN | Native/model closure incomplete; exact next obligation below. |
| `decode_pool_v1_withdrawal_public_v1` | OPEN | Native/model closure incomplete; exact next obligation below. |
| `digest_is_canonical` | CLOSED local | K021; NBG_Atomic.digest_canonical and inherited Array8 shape; all raw eight-limb digests |
| `encode_common` | OPEN | Native/model closure incomplete; exact next obligation below. |
| `encode_pool_v1_private_transfer_public_v1` | OPEN | Native/model closure incomplete; exact next obligation below. |
| `encode_pool_v1_withdrawal_public_v1` | OPEN | Native/model closure incomplete; exact next obligation below. |
| `require_header` | CLOSED local | K026; NBG_Header.header_result/tag_result/slice_equal (L088), all216 bytes, arbitrary magic and both/all enum kinds |
| `transfer_common` | CLOSED local | K022; NBG_Atomic.transfer_projection; every field, all raw public records |
| `validate_common` | CLOSED local | K023; NBG_PaymentChecks.common_result (L076), all raw fields, full error priority |
| `validate_pool_v1_private_transfer_public_v1` | CLOSED local | K024; NBG_PaymentValidators.transfer_result (L079), all raw records, full Result |
| `validate_pool_v1_withdrawal_public_v1` | CLOSED local | K025; NBG_PaymentValidators.withdrawal_result (L079), all raw records, full Result |
| `withdrawal_common` | CLOSED local | K022; NBG_Atomic.withdrawal_projection; every field, all raw public records |

## Native gates and exact remaining work

K019 proves the complete native atomic decoder Option/error and each coordinate on all32-byte inputs. K020 proves one exact encode_digest iteration on arbitrary32-byte pre-state, arbitrary index<8 and raw limb, including every untouched byte. K023/K024/K025 prove complete native common/transfer/withdrawal validator error results on arbitrary raw public records. K026 proves every native header reject/success on arbitrary216 bytes, arbitrary magic and both supported payment kinds. All pass. These passing native gates alone are not credited as complete native/cohort bridges.

Remaining: atomic decoder total/rejecting model association; digest encoder model induction and actual enumerator association; decode_common full byte/error law; encode_common exact writes/frame; enclosing transfer/withdrawal encoders and decoders composed with those closed callees. No whole source loop or whole216-byte codec was unwound.

New NBG_Atomic facts compile (L020), with standard axioms only or none. NBG_PaymentChecks and NBG_PaymentValidators now prove the total common/transfer/withdrawal Result laws (L076/L079); NBG_Header proves every header rejection/success (L088). All receipts retain target,command,exit,wall,RSS,swap,revision/source/dependency hashes and axiom lines. No caller success, desired output, independently selected execution, new cryptographic assumption or runtime trust item is supplied.

One admitted high6G/max8G/swap0/tasks64 scope at a time; Lean-M7000, optimized offline Kani, frozen resolved graph validation before every native run and unchanged lock after. No LPb gate is newly reused. Source/runtime/SDK/P6/allocator/ABI/artifact association stays retained where not closed. RPx_Deployed.deployed, L154 statement parameter, narrowed D188,frozen3,RuntimePersistence and game unchanged. No headline premise removed; S2 and deployed100-bit target unestablished.

No repository shipped/cfg(kani) source change; no ELF rebuild trigger. Inherited, not reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No keys, other worktrees/prefixes, shared launchers or coherent sources modified. No push/merge.

Atomic decoder L074 exhausted DEFAULT200000 elaboration heartbeats in combined
8-word Result/Option normalization. That shape is stopped; no unchanged rerun
or larger limit. NBG_AtomicDecode_PROPOSAL.lean.txt is excluded from importable
modules and closure. Replacement: one-word and rejecting-prefix lemmas, then
composition. K019 remains a full native check, not a model bridge. Digest
encoding K020 is only the arbitrary-state iteration; its model induction and
enumerator association remain open. No codec success/desired output is assumed.

Final checkpoint: NBG_L096 passes the new-module co-import/84 selected-root
axiom audit with standard axioms only; exact receipt and source hashes retained.
NBG_GRAPH_AUDIT.json covers every actual native run. Final K032 formatter gate
timed out without error-bridge closure; no rerun or raised limit. Budget STOP:
30 Kani and95 Lean invocations. NBG_HANDOFF.md is the final self-contained
claim/trust/validation/blocker handoff; NBG_END.json records terminal scopes,
unchanged start cache/Aeneas pins and owned target/solver cleanup.
