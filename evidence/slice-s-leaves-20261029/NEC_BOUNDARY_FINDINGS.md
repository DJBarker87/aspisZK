# Slice boundary findings

## Ledger snapshot
Unchanged NDT_validate.py rejects even the unchanged authoritative ledger copy after NEC stage commits: "merged report corpus changed; refresh evidence snapshot explicitly". The earlier sparse import error was resolved by materializing unchanged NDK/NCZ files. No shared validator/infrastructure modified. A lead snapshot refresh is needed before a current-head proposed delta can pass recomputation. No composed row is promoted meanwhile.

## Emission slot effect
AdapterRw.Ops.op53 is Statement → Result (Result Unit ProgramError); frozen emit_result also calls program::set_return_data. Ruling (s) requires representability/frame and same-argument call-site association, and does not by itself erase this runtime write. Existing NDO_JHb_Emit.source models the explicit return-data state, while NDO_JHb_EmitAdapter.source projects it away. This worker has not established the native runtime call/effect association to that projection. Emission correctness is not added as a soundness premise; the native slot instance and effect/frame projection remain OPEN. Need native exact set_return_data buffer/length/call-prefix transport plus the adopted ReturnData runtime/projection law, not a constant-success op53. No SHA unwinding or runtime implementation changes are proposed.
