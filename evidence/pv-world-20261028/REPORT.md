# World interpretation result — D364 resume

**Target not established. No row closed; no endpoint premise removed.**
Stopped on budget exhaustion: 100/100 Lean compiler starts total, including
96 resumed attempts; zero Kani. Final focused audit and replay passed. W-CARRIER-1 is a finding about a design that
forgets destructor-accessible state, not a ledger/endpoint counterexample and
not a stop. The earlier report's stop disposition is superseded.

Exact worktree `/Users/dominic/ZK/.worktrees/pv-world`, unchanged branch
`codex/pv-world-20261028`; resume start `937b8f561de14683239b9f5f7abe74c7eafd013c`.
Original prover base `10b8afe7647d478f70693d8fc12e07be871c91e0`.
Host directory `/home/dombarker/project-offloads/codex-pv-world-20261028/`.
Used IDs: 36000–36096 and 36197–36199, all within the assigned block.
Original uses were 36000–36002 and 36197; final audits used 36198–36199. `REFUSALS.md` records uncharged admission cooldowns.

## Established focused results

`PV_W_Enriched` retains process statics/atomics, live heap allocations and
ownership, allocator state, thread-local cells, volatile writes, ordering and
fences, unwind state and runtime-specific Extra. Its flag/counter witness
represents both retained normal/panic outcomes, counts one destructor entry,
and records an internal event. `drop_valid` and `project_threaded` establish
full-world continuity and OS projection through proven-silent steps. This is
not a proved representation of the shipped machine or all reached destructors.

`PV_W_Syntax` proves the typed state/error/trace interpreter agrees with an
independently defined operational execution judgment, including early-error
and divergence prefixes. `PV_W_SourceSyntax` supplies complete-Result erasure
and named bind/branch laws. These are model/source laws, not native purity.

`PV_W_Reservation` reifies the exact frozen directory-sync, fallible-reserve
and public store-reserve bodies. All three complete-Result erasure theorems
compile. The checked generator retains all 34 source call sites, arguments,
continuations and error branches. The finite source-tree proof generator
replaced unsuccessful congruence searches; caps were never raised.
`PV_W_ReservationThreading` composes those concrete source terms with ordered
operational world threading and enriched-state projection.

`PV_W_TypedEffects` and `PV_W_TypedReservation` retain typed open/sync/options/
error-kind/write arguments, with dictionary families for emitted generic
path conversions. Their erasure remains exactly the frozen Result.
`PV_W_TypedThreading` proves caller composition from local model-step laws;
those laws remain explicit obligations. Helpers are not asserted natively pure.
`PV_W_ErrorSyntax` proves error embedding preserves complete state/trace
results, allowing interpreter tape faults to remain distinct from native IO
error values. Focused receipts include their axiom reports.

## Still required

The requested **entire extracted prover → existing trust Observation** theorem
is not established. The exact `prove_masked_attempt` entry reification
(16 call sites) and complete-Result erasure passed, as did entry threading
conditional on local model-step laws. `PV_W_OsFile`, `PV_W_OsEntropy`,
`PV_W_OsSchedule` and `PV_W_OsCombined` interpret the actual existing OsWorld
tapes and prove reservation projection to its ordered tagged-call sequence.
They preserve native error payloads separately from tape faults and retain
process/filesystem updates. `PV_W_RepeatFile` checks an advancing repeated-call
model; it is not a native O_EXCL proof. These results do not establish
primitive native adequacy or bind a complete trust-field Observation. The main nested proof routine,
reservation_path and other helpers still need recursive interpretations;
primitive native adequacy, actual reached Drop/implicit close and ownership,
allocator/zeroize fidelity, and the complete filesystem/D159 observation
producer and deployment binding remain P obligations. No partial threading
lemma is counted as that complete theorem or a native dictionary installation.

The original FXM native witness is retained at its committed pins. No new
reached-destructor purity theorem is borrowed from unfinished/unavailable
fxmem2 work. The original fixed-callback/forgotten-state findings remain
findings; they do not stop this resume.

## OS findings and row accounting

W-OS-1: O_EXCL exclusive creation/namespace behavior remains an owner finding.
W-OS-2: file sync and parent-directory-entry crash durability are distinct
owner obligations; nonce non-reuse across recovery depends on the required
persistence/recovery laws. Neither is assumed, and neither is a new T field.
OS-FINDINGS.md gives the dependencies. Native IO failure witness independence
under the adopted public-failure option is still unproved here.

V170 effectful cases and V171/V172/V175/V176/V267/V268/V271/V221/V222 remain
OPEN at their ROWS7 scope (`row-scope.json`). Endpoint statement, carriers,
observer (including L1/L2/L3), simulator, failure event and T are unchanged.
T remains exactly entropy_law, entropy_kernel, observation. Premises
removed/added/weakened: **0/0/0**. No source refinement gap is hidden in T.

## Validation boundary

Lean runs use one capped scope at a time: MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, -M7000. Exact commands, source revision/blob/SHA,
dependency fingerprints, exit, wall, RSS, swap and axiom output are retained.
Only successful standard-axiom results receive credit; failed sorryAx output
is rejected. No Kani, Rust/SBF rebuild, key/account operation, merge or push.
No changes under crates/ or programs/, frozen extraction, shared source tree,
or soundness/deployment files. No XR imports or proof shortcuts.

All 5,673 h4 external objects were hash-verified before the first resumed
compile. Split-object companion selection and the public-import scan repair
are documented. CACHE-SCAN-CORRECTION.md supersedes the initial incomplete
OS cache preflight; the failed consumer passed after full revalidation.
No unchanged full regression or full frozen manifest replay was run: no
row-closing native/deployment instance has been obtained.

History: `git log --oneline 10b8afe7647d478f70693d8fc12e07be871c91e0..HEAD`.
Final source/receipt accounting is `resume-validation.json`: 100 compiler
starts (76 accepted and 24 failed), no unverified focused sources, and no row closures. Final targets:

| ID | Target | Exit | Wall | Peak RSS (KiB) | Swap |
| --- | --- | --- | --- | --- | --- |
| 36198 | R1Z/PV_W_ResumeAudit | 0 | 1.50 s | 3856952 | 0 |
| 36199 | R1Z/PV_W_ResumeReplay | 0 | 1.53 s | 3859612 | 0 |

The audit contains 93 explicit axiom queries; the replay adds six. Every
accepted query uses only a subset of propext, Classical.choice and Quot.sound.
Exact source revisions and source hashes are recorded per attempt in
`36198-source.json`, `36199-source.json` and their receipt directories,
with the final module hashes in `resume-source-freeze.json`. This is a
focused dependency/import replay, not a full deployment-manifest release.

`resume-cleanup.json` and `resume-private-object-manifest.json` retain the
compiled-artifact inventory/hashes. Cleanup removed 22,148 private entries;
zero reused targets were removed. Sources, receipts and witnesses remain;
no keys were touched.

Next concrete deliverable: recursively interpret `prove_masked_with_attempt`
and reached helpers, prove native primitive/Drop/ownership adequacy for their
actual types, then connect the resulting full filesystem and D159 payload
sequence to the existing Observation producer without adding any T premise.
The source/model results here provide composition lemmas for that work, not
a substitute for it.
