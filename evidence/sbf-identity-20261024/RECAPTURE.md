# Proposed next identity gate — NOT RUN

This is a missing-evidence-artifact rerun rationale under AGENTS rule 5, not
permission to run in this job. Exact three mode argv, environment, output paths,
ELF hashes/sizes, wrapper pin and historical predecessor receipts are in
`recapture-plan.json`. Execute sequentially, never three simultaneous scopes.
Expected time is optimized compilation/diagnostic emission, not proving. No
protocol, feature, dependency lock, backend, source, P7 meaning or security change.

## Before authorization and before any build

1. Release custodian supplies an immutable read-only export of the released
   `/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023` workspace's
   `sbf-target-verifier` and `sbf-target-pool`, with a complete cache manifest,
   compiler/dependency provenance and recorded freshness/ownership assessment.
   These are the named warm predecessors, not other workers' active caches.
   We have **not** inspected or fingerprinted these caches this job. Only their
   released outputs/receipts and top-level presence were assessed. Authorize a
   read-only snapshot from the custodian, then reflink/copy into the new stage's
   corresponding private targets; never mutate the donor. Verify the snapshot
   manifest before and after copying and record every reused object. Missing
   provenance, incompatible tools/fingerprints, or a need for broad dependency
   bootstrap stops this gate and returns to lead; do not quietly rebuild all.
2. Materialize the exact 7,978 input manifest records at frozen source
   `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` into the new stage from immutable
   Git objects. Manifest SHA-256 is
   `a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1`.
   Retain exclusions and verify every file's bytes/type/mode, workspace config,
   build scripts, target config, manifests and lock. No extra source inputs.
   Cargo.lock SHA-256 remains
   `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
   Reject missing Git objects; do not substitute a live checkout. Preserve keys;
   no wallet/SDK fixture key is needed or authorized. Wrapper is copied from the
   immutable tracked blob and verified against the explicit plan digest.
3. Official archive metadata: platform-tools tag v1.52 resolves to
   `e3ebfccfe63ba936dd6951ede390496c6bc2f296`. Linux x86_64 archive is
   519270959 bytes, official API SHA-256
   `8b3861e93daf085ec12b65c4fac374d9bec4587a3de16871da6b08ab0c1d907e`.
   No archive was present at the inspected v1.52 global packaging root and none
   was downloaded. A custodian must supply a retained checksum-matching archive,
   or lead must separately authorize acquisition outside this job. Compare the
   complete relevant archive members, symlinks, sizes/modes and bytes against
   installed tools, runtime libraries, all target archives and rust-src. Do not
   claim official binary equality from version.md alone. No install/update.
4. Retain official Rust commit `790f1537507dbdb0da320fbb3b1c1eca3b33c474`,
   its library tree, declared LLVM gitlink
   `78496716176191b2dfb728e5e38501812e7467db`, cargo/newlib declarations,
   archive checksum, build script/workflow hashes and matching rust-src manifest.
   Source correspondence is packaging evidence; compiler correctness stays P7.

## Pre / go / post capture (each mode separately)

Write fresh `capture-<mode>-v1/{pre,go,post}-identity.json` in the new stage;
this job's current hashes cannot serve as future go measurements. Resolve all
links first; reject private/live targets, missing files or any content/version
change from the reviewed current baseline. Pin SHA-256, size, mode, symlink chain
and full version output for cargo-build-sbf, rustup proxy plus resolved host
cargo/rustc, host compiler runtime and build-script sysroots, SBF rustc plus
librustc_driver, rust-lld and gcc-ld shim, LLVM linker/objcopy and runtime/newlib,
all sbpf target archives, and complete rust-src. Pin target selection/cfg,
Cargo configs including CARGO_HOME, environment allowlist, lock, input/dependency
source manifests and complete cache constituents. Expand from the captured
baseline to all actual subprocess/runtime inputs; an unmanifested input fails.
Verify registry archive checksums AND unpacked source bytes against Cargo.lock;
do not infer consumed bytes from package names. Never read keys. Record actual
compiler commands and library/dependency paths; require the expected selected
SBF compiler, target and optimization on every selected crate.

Pre happens after materialization/cache copy. Go happens under the approved
admission/coordination path immediately before the command; post immediately
after completion. Ensure no concurrent writer can mutate tools/source/caches
between these observations; otherwise content snapshots alone are not a
proof of time-of-use identity. Mark changed or unknown inputs as failure.
Force selected frozen owned crates through compilation in **own** private cache
(e.g. advance their mtimes, retain before/after content hashes); stale diagnostic
files cannot count as emitted evidence. Retain per-mode outputs before the next
mode; preserve default/devnet separation and explicit devnet program IDs.

## Resource admission and execution

Use the lead's existing strict admission runner, unchanged. No new resource gate
is implemented/adopted by this packet, and the proposed ResourceSLAB73658
half-reclaimable credit is forbidden. Before AND at go, record all populated
hierarchies, finite disjoint ancestor reservations, exclusive uncapped charge,
current-minus-inactive-file charge, MemTotal/MemAvailable and 7 GiB control
reserve. Finite reservations including requested 8 GiB must be strictly below
55 GiB; existing strict uncapped/resident/MemAvailable gates must all pass,
without slab credit or double-counting nested cgroups. Missing/raced data deny.
If the approved strict runner/pin is unavailable, **do not launch**. Historical
S10 reservation.py's weaker admission is evidence only, not a substitute.

Each independent scope is exactly MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. Preserve an existing stricter 5G/7G scope;
never raise it. The plan records `/usr/bin/time -v` and timeout600; also retain
scope memory.peak, memory.events, swap current/peak, limits, aggregate child RSS,
stdout/stderr, target progress and exit. Stop at ten minutes without a new
target; no unchanged OOM retry or cap increase. Acquire the existing shared
launcher/global lock if required by current scheduling; this plan runs no Lean
and does not introduce a second lock around an existing launcher.

Historical predecessors (reused, not new): default 31.913s / 686076 KiB process
RSS / 1176027136B cgroup peak; devnet 31.480s / 683772 KiB / 1174343680B;
Pool 32.529s / 678960 KiB / 1138647040B. All exited0, swap0, under 6G/8G/
noSwap/Tasks64; exact commands and individual cgroup names are preserved in the
plan. Stale receipt source b2727acd is corrected by the independent 4bb3 source
manifest, not silently rewritten in raw evidence. These warm predecessors
justify a focused replay, not a cold dependency bootstrap or lower caps.

## Acceptance and claim limits

All three output hashes must equal their exact current pins in the plan;
compare linked and deployed outputs, sections and new emitted diagnostics to
retained Port24 associations. Check full output bytes, not just text/symbols.
On any mismatch stop, preserve failed outputs as remote hash+size plus logs,
classify the cause, and do not force consumption of the desired ELF or amend a
pin. No automatic retry with altered features, tool versions, locks or source.

A pass establishes a **new captured build association** under unchanged P7 and
explicitly assessed reused cache inputs. It does not establish past S10 source
identity, compiler correctness, source-to-native semantics, primitive ordered
fault/oracle effects, or either deployed security target. Existing Lean/Kani/
Port24/runtime results remain explicitly reused under their own revisions;
no full manifest or unrelated regression is requested. New Lean/Kani/extraction
budgets remain zero unless the lead separately assigns them. All reports must
retain source/dependency/tool pins, target argv, exits, wall/RSS/swap and N/A
#print axioms for non-Lean work. Large JSON: hash+size only; no binaries committed.
