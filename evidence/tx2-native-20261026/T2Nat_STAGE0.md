# TX2 native stage 0

S2 OPEN; target not yet established. Assigned rows L175 and L172 remain open.
Base revision a4ac35e18f, branch codex/cx-tx2-native-20261026.

The requested older root paths resolve in docs/research/100bit-spend-path-20261013/.
Their hashes, current joint top, ledger and coherent workspace are pinned in
T2Nat_inputs.json. Route B is already adopted; no new trust item is requested.

Before: CPhy_Physical retains Tx2N Outcome's Boolean FinT transport; reader
uses Port4A with reference helpers. Full finish Result/errors/log and bounded
native-helper composition remain implementation obligations, not crypto assumptions.

Plan: first reify the emitted finish control, proving full Result and unchanged
ordered oracle log, then specialize to the actual returned accumulator. Next
compose current reader helpers on the same retained bytes and actual op18 call.
No shipped source changes are planned. Allocator/runtime/TrustedStd/P6 and the
existing arithmetic owner boundaries remain explicit.

Ledger delta: removed NONE; added NONE. No prover result or new non-vacuity
claim yet. Host preflight: only init.scope populated. Use existing launcher,
Lean -M7000, MemoryHigh6G/MemoryMax8G/Swap0/Tasks64, one focused module/attempt.
Budget used 0/100 Lean, 0/30 Kani. No keys, artifacts or other prefixes touched.
