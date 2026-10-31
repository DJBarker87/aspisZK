# Slice boundary findings

## Ledger snapshot
Unchanged NDT_validate.py rejects even the unchanged authoritative ledger copy after NEC stage commits: "merged report corpus changed; refresh evidence snapshot explicitly". The earlier sparse import error was resolved by materializing unchanged NDK/NCZ files. No shared validator/infrastructure modified. A lead snapshot refresh is needed before a current-head proposed delta can pass recomputation. No composed row is promoted meanwhile.

## Emission slot effect
AdapterRw.Ops.op53 is Statement → Result (Result Unit ProgramError); frozen emit_result also calls program::set_return_data. Ruling (s) requires representability/frame and same-argument call-site association, and does not by itself erase this runtime write. Existing NDO_JHb_Emit.source models the explicit return-data state, while NDO_JHb_EmitAdapter.source projects it away. This worker has not established the native runtime call/effect association to that projection. Emission correctness is not added as a soundness premise; the native slot instance and effect/frame projection remain OPEN. Need native exact set_return_data buffer/length/call-prefix transport plus the adopted ReturnData runtime/projection law, not a constant-success op53. No SHA unwinding or runtime implementation changes are proposed.

## Partial header domains are not callable full packets
The statement/request/late input-prefix harnesses explicitly require their accepted header partition. Their real slice callers supply arbitrary encoded bytes, so those callers do not establish this partition unconditionally. These passes are input-fragment evidence only and remain OPEN under NDT semantics. Invalid-header cases, complete child/error/return composition and actual caller domains must be joined before proposing a whole packet. K050 arbitrary-kind request and K059/K060 separate request kinds all timed out; no request input-prefix credit.

## Outgoing foreign ProgramError contracts
The inherited exact Result<Box<Statement>,ProgramError> verified-substitution fidelity control NDM_K083 is a compiler rejection (no kani::Arbitrary for foreign ProgramError; orphan rules forbid a scratch impl). It is not a failed semantic control and does not clear that interface. No such verified substitution is used here. A new Result<(),ProgramError> control family is planned before relying on the emission contract; if its corresponding verified control is rejected, actual body/prefix checks remain fragments and no composed contract credit is claimed.
