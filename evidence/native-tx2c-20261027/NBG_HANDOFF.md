# NBG TX2 continuation handoff — budget stop, target not yet established

## Claim and exact remaining obligations

U01's 47 assigned arithmetic/carrier members have local hybrid native/Lean
bridges on the domains in [NBG_U01_BRIDGE.md](NBG_U01_BRIDGE.md). This includes
the full raw-u32 inverse result (zero assertion included), canonical tower
arithmetic, optimized square bounds, and exact byte carriers. Multiplication
uses the owner's translated-field method, not native Kani multiplication.
The caller must establish each recorded domain; these helper bridges do not
establish enclosing callers or installation of their dictionaries.

U00 remains OPEN with exactly `filled` and `error`. Observer, mark and value
reuse NBC's CLOSED bridges; digest has a CLOSED local forwarding/reply bridge
with runtime digest realization retained. K005 checks exact descriptors, one
call and unchanged reply; the universal slice forwarding argument additionally
uses the frozen unbranched wrapper body. It does not infer arbitrary lengths
from bounded native tests. See [NBG_U00_BRIDGE.md](NBG_U00_BRIDGE.md).

U02 has eight CLOSED local members: `unwrap_fixed_slice`,
`digest_is_canonical`, `transfer_common`, `withdrawal_common`, `require_header`,
`validate_common`, `validate_pool_v1_private_transfer_public_v1`, and
`validate_pool_v1_withdrawal_public_v1`. Exactly eight remain OPEN:

- `decode_digest_canonical` and `encode_digest_canonical`;
- `decode_common` and `encode_common`;
- `decode_pool_v1_private_transfer_public_v1` and its encoder;
- `decode_pool_v1_withdrawal_public_v1` and its encoder.

[NBG_U02_BRIDGE.md](NBG_U02_BRIDGE.md) distinguishes full native decoder checks
from the missing model association, and one encoder iteration from a whole
encoder bridge. No native-only gate is credited as a complete bridge.

## Assumptions and association

No headline premise, protocol assumption or runtime trust item is removed,
added or changed. The headline remains `AspisR1.RPx_Deployed.deployed`; L154 is
a statement parameter, D188 is narrowed, frozen3 is adopted, and approved
RuntimePersistence and game fields remain. S2 and the deployed 100-bit target
are **not yet established**. These are local P6 obligations of the narrowed
trust boundary. `verifier::prepared_claim` was already closed by LPt; its
existing report is referenced, and this continuation claims no new closure
of it. TX2 does not call prepared_claim again; its upstream saved-checkpoint
domains retain the approved persistence/game/account association. Fresh TX1
producer hypotheses are not treated as a TX2 execution.

Native gates discharge the recorded arithmetic/control/byte-step associations
only on their stated domains. Lean establishes the corresponding exact model
Results, bounds, error priority and loop induction. Field stubs, their named
emitted-ok theorems, and caller domains are in [NBG_STUBS.md](NBG_STUBS.md).
K028 is one arbitrary-prestate iteration; NBG_SquareTrace derives the SAME raw
model Result from its per-cell relation. NBG_INV_SOURCE.json checks every
ordered call/operand in the fixed inverse DAG. No whole loop or SHA is unwound.

The coherent SInt2 objects select digest/error slots op43/op44; original
inventory attribution is corrected in NBG_COHORT_CORRECTIONS.md. FIo and RPz7
field declarations are byte-identical except import names, with whole-file
pins in NBG_FIO_SOURCE_SELECTION.json. Different dictionaries are not equated
silently. NBC modules, SAQ/R72 inverse, LPf/LPi field/byte proofs and the
existing P6 writer induction are reused unchanged. Minimal-import generic
utility proof-body replays are explicitly recorded, not new protocol axioms.
No XRn_Join kit or stand-in is used.

Retained boundaries include runtime hash/log realization, actual caller
dictionary installation, SDK/allocator/ABI/platform/compiler/P6 association,
and source-to-ELF association. The failed formatter gate discharges none of
its allocation/failure/cleanup obligations. Closed helper domains have not
been promoted to universal parent-call preconditions.

## Validation actually executed

Frozen native source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Frozen lock SHA256:
`5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
All research/repository crates and programs match that revision
(NBG_REPOSITORY_SOURCE_CHECK.json). Scratch changes are only six appended
cfg(kani) declarations plus six NBG harness files; frozen bodies are checked
byte-for-byte against the 1,234-file manifest (NBG_END.json).

Budget consumed: **30 actual Kani commands / 95 actual Lean commands**.
K001/K002 and L006 are setup-only identifiers, not prover invocations.
No further proof launches after K032. K005–K031 pass; K003/K004 fail compilation,
and K032 exhausts its fixed 90-second harness timeout. L074 exhausts default
200,000 elaboration heartbeats; its proposal is excluded from importable Lean.
Neither stopped shape was rerun or given more resources. Other rejected local
attempts and own wrapper repairs remain in NBG_FAILURES.md and raw receipts.

Final new-module co-import and selected-root audit: `NBG_L096`,
`lake env lean -j1 -M7000 -DElab.async=false … NBG_Audit.lean`, exit0,
wall3.753845958970487s, peakRSS5,074,236KiB, swap0, source revision
`f18acc99e7ec66f5dc5996c253ce3cd9b6ce6e39` plus exact recorded source hashes.
Its 84 selected `#print axioms` results use only `propext`, `Classical.choice`,
`Quot.sound`, or no axioms. Each new top theorem also has its own print audit.
Rejected diagnostic `sorryAx` lines are not accepted results.

All actual prover/build commands ran serially in admitted scopes with
MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64; Lean used -M7000.
Admission required exit0 and JSON allowed:true. One reservation refusal was
waited out before launch. Maximum recorded child RSS was5,277,488KiB; all
swaps0. Exact targets, commands, exit statuses, wall times, RSS, cgroup peaks,
source revisions/hashes, dependencies and axioms are in each receipt and
NBG_VERIFICATION.json. Counts/import success are audit metadata, not security
progress substitutes.

Before EVERY actual Kani run, offline cargo metadata was validated against
the frozen package/version/source and dependency-edge selection; the lock was
unchanged after every run. NBG_GRAPH_AUDIT.json retrospectively applies the
stricter unambiguous-edge check to all saved metadata without rerunning Kani.
The 441 selected packages exclude three unused frozen workspace packages,
as in LPd's package-selection method; this is not a claim that all optional
lockfile packages/edges were built. No new/drifted package or edge is present.
Kani used the pinned 0.67.0 binary, optimized profile3 and CARGO_NET_OFFLINE=true.
No LPb stage is credited and no cfg-if/libc drift exception is taken.

No full frozen release-manifest replay, adversarial/runtime suite or SBF
rebuild was run: the target remains open and shipped sources did not change.
Inherited ELF pins are retained, **not reproduced**:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`;
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`;
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.

## Host state and next deliverable

Host workspace:
`/home/dombarker/project-offloads/codex-cx-native-tx2c-20261027`.
Coherent SInt2 and other workers' files were read-only. Missing unchanged
dependencies were built once (44 successful targets), exclusively into
`/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027`.
All 189 start-cache files retain their hashes; end inventory contains373 files.
All219 actually selected Aeneas object pins are unchanged. The persistent cache
is retained, including new NBG objects. NBG_CACHE_START/END.json and
NBG_LIBRARY_START/END.json record every selected object. Immutable backend and
tool hashes match inherited pins. All125 receipted proof scopes are inactive/dead.
Only owned NBG_target (1,991,451,781 bytes) and NBG_tmp were removed, after
terminal checks. Frozen scratch sources and proof sources remain for recovery.
No keys were created, removed or operated; no shared infrastructure, candidate,
other worktree or other prefix was changed. No push or merge.

Next deliverables are (a) a native reserve/resize ownership/effect bridge for
`filled`; (b) split enum-formatting/write-step plus log and allocation/failure/
cleanup association for `error`, never the timed-out whole formatter again;
(c) one-word/rejecting-prefix atomic decoder lemmas, encoder model induction
and enumerator association; then (d) common/full payment codecs composed along
their real call dependencies. These require a new worker budget. No action is
held behind unrelated open units.

Stage commits before this final evidence commit: f21ade1bf2, 1f4a3b4006,
c2bf6cb9f0, f18acc99e7. Branch `codex/cx-native-tx2c-20261027`; commits local only.

Final source-policy inspection found only owned evidence/NBG paths, no binary
artifacts and no forbidden proof admissions/options in the24 new Lean modules.
The broad whitespace check reports preserved raw-log trailing whitespace/EOF
blank lines (NBG_DIFF_CHECK.log); raw receipts were not rewritten.
