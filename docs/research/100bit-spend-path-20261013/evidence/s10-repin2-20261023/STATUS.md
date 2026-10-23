# S10 owned-adapter re-pin — 23 October 2026

## Stage 1: adopted artifact reproduction

Compiler input revision `d50042542971c7a11bab8c3662896ccf834daa59`.
`source-inputs.json` pins all 7,978 retained workspace inputs. Relative to
S10's 22 October snapshot (`7acf5cfb5fa49f4cf5d8e69566ba8221189c31ac`), five
files change: three `r1_pool_adapter*.rs` files, test-only `lib.rs` wiring
and `adapter_rw_tests.rs`. `source-delta.json` records the exact deltas.
The child source inputs are unchanged. No shipped file is edited by this task.

Build receipts and artifact comparisons are retained in `build-manifest.json`.
Each optimized SBF build uses its own MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64 scope and `-j 4`. Time is expected in optimized
compilation and MIR/LLVM/mono diagnostic emission, not finite-field elimination.
Platform tools are v1.52, with the retained features and devnet program IDs.
Raw compiler stack-frame diagnostics remain visible: artifact reproduction
alone is not a runtime safety or semantic refinement claim.

Two unsuccessful setup attempts remain recorded. Default-v2 failed before
compilation because the copied diagnostic wrapper lacked its executable bit;
restoring that mode allowed default-v3. Devnet-v1 was launched too early and
was stopped while Cargo waited for the private target lock (no devnet crate
compiled). The replacement launcher holds a private workspace lock through
artifact and diagnostic capture; devnet-v2 then runs after default capture.
Neither failure was memory pressure. No cap was raised.

The reused receipt harness writes historical revision `b2727acd`; this is
not the compiler input revision. `build-manifest.json` explicitly corrects
that field using the independently rehashed snapshot, retaining raw receipts.
No binaries, objects, tarballs or wallet keys are committed. Cargo-generated
keys stay securely on the private host; no keys are cleaned up.
No Lean process is started. `#print axioms`: N/A for this compiler evidence.
Historical pass 1–5 and 22 October certificates remain untouched.
S10 completeness and S2 caller identities remain open; target not yet established.

All three successful builds reproduce the adopted pins:

| Mode | SHA-256 | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|
| default | `d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0` | 34.960 | 686600 | 0 |
| devnet | `2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922` | 35.499 | 686536 | 0 |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 34.962 | 676788 | 0 |
