# S2-X: owned boundary, stage 1

Target: adopted owned caller (D182), branch codex/cx-s2x-20261023.
No shipped source, other worktree, existing Lean module, key or artifact changed.
Required release pins: default d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0,
devnet 2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922,
Pool 121f3e29… (unchanged). No rebuild triggered by additive proof work.

## Actual extraction boundary and obstruction

AdapterRwModel.Ops has fields op0–op53. They are comparison/range,
verifier/digest, sizing/tag, statement/registry/scan/PDA/emit operations.
**They are not 54 SDK snapshot/copy/write operations.** The extracted
stage1_owned and stage2_owned take already-owned account records. Native
snapshot (r1_pool_adapter_owned.rs:29–43), stage1 entry/write (:445–463),
and stage2 entry (:465–482) are outside that extraction.
S2TrustedSdkBorrow covers acquire/deref/write/drop, not Vec allocation,
to_vec, memcpy, snapshot metadata construction or native wrapper lowering.
RuntimeEntrypointAdmission does not supply these source refinements either.

ChildInputRetention in AdapterRwLeadInputs quantifies c before *all* child
arguments. S2X_ChildRetention.retention_requires_unique_second_proof proves
that it forces any two successful op11 calls to have equal proof arguments
whenever c has one reached late site. retention_obstruction rejects that
port if two distinct proof arguments succeed. Arbitrary opaque Ops permit
this (for example a constant successful op11). This is a contract obstruction,
not a deployed verifier counterexample. The universal interface cannot be
instantiated from purity alone. Existing successful source proofs are not
invalidated; their retention hypothesis remains explicit.

owned_retained and second_owned_retained prove the narrower valid fact:
fixed owned arguments remain equal to themselves after pure application,
for arbitrary results/errors. They do not produce internal site observations.
A source-indexed observation join is still needed, scoped to the one actual
invocation rather than all successful invocations. No existing file is edited.

## Validation

Exact focused receipts, commands, source snapshots, selected cache hashes,
source revision, wall/RSS/swap and complete axiom reports are retained per
attempt. Host scopes: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64; -j1 -M4400, cached dependencies, no cap changes.
Kani: 0/60. Full release replay not justified while source joins remain open.

## Stage 2: SDK write and accepted checkpoint length

S2X_SnapshotWrite.owned_data proves the actual extracted OwnedAccount.data
success branch projects the same owned vector without consulting Ops.
full_copy proves the existing Aeneas std full-slice copy returns exactly its
source when lengths agree, symbolically (no concrete 1768-byte evaluation).
accepted_checkpoint_length uses the actual whole-stage1 accepted-return
inversion and the fixed account2 snapshot to derive returned length 1768.
Its remaining condition is OwnedSnapshotShape plus entrySize on the snapshot:
the native snapshot wrapper still must establish its data/length representation.

sdk_write instantiates exactly the existing exclusive_deref SDK trust field;
sdk_write_frame proves its mathematical byte update preserves ambient state,
account-cell mapping, counters, guards, all descriptors and other payloads.
commit_frame/commit_metadata/commit_bytes prove the complete Account-record
properties of a CP-only commit. This is a logical commit specification, not a
claim that the native memcpy/write wrapper has been extracted or joined.
The actual source-to-spec copy/metadata/child effects remain open.

Lean002 failed on elaboration errors (constructor namespace, deref projection,
projection syntax and conditional simplification). It is retained and excluded;
Lean003 changed the source and passed: exit0, 2.318372s, 4394168KiB, swap0,
eight standard-only axiom reports. Lean001: exit0, 2.005779s, 4382484KiB,
swap0, four standard-only reports. No timeout/memory-kill or cap increase.
