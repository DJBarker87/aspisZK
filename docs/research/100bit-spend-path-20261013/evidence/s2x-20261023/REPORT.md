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

## Stage 3: transaction runtime split and opaque effects

S2X_RuntimeRetention.tx2_proof_binding applies the EXISTING
R9PoolRuntimeBinding.P2Prime to the EXISTING digestMatches on complete
consumed proof/public inputs. It does not assert proof-account owner sealing
or immutable raw account contents between transactions. tx2_suffix combines
that premise with the actual checked source range, original byte projection
and raw account length; the candidate prefix may change.

history_retains proves account persistence under a transaction history with
no intervening committed write to the protected key; rollback is an identity
step. CheckpointVersionBinding names the exact still-uninstantiated operational
interpretation for a saved/loaded checkpoint: authenticated ledger key/version,
savedAtCommit, loadedAtEntry and noInterveningWrite. checkpoint_persistence
proves loaded=saved from it. checkpoint_sites propagates that to the actual
Required14 field type under the separately named saveCut/tx2Cut/resumeCut
observations. None of these premises is inferred from TX2 readonly flags.

P2 covers physical persistence, permission enforcement and rollback; P3 covers
the authentic address/System semantics used by the source; P4 covers faithful
runtime metadata observations. The source must still show that its authenticated
save/load cuts select this same protected account version. BoundaryStatements
P2/P2_prime/P3/P4 remain opaque Prop slots: no implication from those slots to
these operational statements is claimed. CheckpointVersionBinding is an explicit
missing interpretation/history obligation, not an adopted new runtime axiom.
In particular P2 cannot itself forbid an authorized intervening write. No SHA
injectivity or new collision budget is introduced. R10 observation/log provenance
remains a separate source obligation, as in STORED-CARRIER-20261021.md.

OpaqueChildFrame names the native frame still needed for opaque calls: all full
account records, all runtime data-borrow counters and caller guard ownership,
and contents/descriptors/liveness of every caller-owned input allocation.
Child-private allocation and ordered oracle state may change. The frame is not
asserted from the pure Ops type. It is a source refinement obligation, not SDK
trust. The pure retained-argument result does apply even to an opaque Ops value,
but supplies no native effect or internal reached-site observation.

ChildRetention additionally contains constant_second_obstruction: replacing op11
with a constant successful PURE function (permitted by the actual extracted Ops
type) contradicts universal ChildInputRetention at a reached late site with two
distinct proof arguments, with no successful-call hypotheses left to assume.
This is a concrete interface-model counterexample, not a deployed runtime attack.
Fix the port to quantify the invocation arguments outside its site assertions,
and derive the observations from that SAME child execution before installing it.

Lean004 was a preflight-only cache miss, not a Lean launch. Existing R9 proof
objects were copied from recorded local cache roots into this worker's PRIVATE
host cache; top R9 object SHA256 matches the stored-carrier receipt's direct pin.
Their hashes/sizes and current source hashes are in reused-cache.json; this is
reuse, not a coherent source/dependency rebuild. No shared object was overwritten.
Lean005 (stronger child obstruction) passed. Lean006/007 failed on name/parser
and scalar-notation elaboration, respectively; changed Lean008 passed with five
standard-only reports: exit0, 2.387586s, 4400492KiB, swap0. Failed recovery
sorryAx output is retained and excluded from accepted evidence.
