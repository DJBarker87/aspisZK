# SbfSeal source-only handoff

Branch codex/cx-sbf-seal-20261025; entry50ab99cfbf. Criteria43b2e5eb6a committed
before implementation8a9c33dd39. Only the two assigned paths changed. No merge,
push, delegation, host/SSH/network/download, privilege/root/namespace/mount/scope,
GO/measurement, Cargo/rustc/Lean/Kani/backend/extraction/native-probe/ELF/key/RPC
operation. Small ordinary local Python tests and immutable local Git reads only.

## Established source progress

New SbfSeal_setup.py replaces the old unsafe implementation as a candidate in
NEW paths; the original disabled SbfClosure helper is unchanged. No import or
CLI activates privilege. privileged_entrypoint always raises before effects,
even if APPROVED_MANIFEST_SHA256 is edited. No arbitrary root command/argv/UID/
path admission API exists. Generic filesystem utilities are ordinary library
primitives, not privileged endpoints. There is no runnable Linux backend.

* create_fixed_layout is concrete unexecuted fd-relative construction under
  fixed /var/lib/SbfSeal-20261025-v1. ALL root-owned, non-group/world-writable
  ancestors open componentwise O_DIRECTORY|O_NOFOLLOW before mkdir. No user-owned
 0700 ancestry, symlink/resolve race claim, sticky-parent exception or existing
  entry reuse. Exclusive descendants use pinned parent fds; subsequent identity
  comparisons are supplemental checks, not the reason a hostile rename is
  impossible. Premise: no root/capable adversary can modify those ancestors.
* Capture copies finite single-link regular files by fd, O_EXCL|O_NOFOLLOW
  destination creation, bounded reads, pre/post metadata/content and destination
  rehash; fchmod only by fd. Modes444/555 and sealed directories555, then closes
  all destination write handles before any future fork. No hardlink, symbolic
  destination link, pathname chmod/chown, recursive bind, HOME/cache or /usr bind.
  Errors retain partial material and cannot reach execution. A full runtime
  mapping is deliberately absent: this is not a Cargo-sized copy policy.
* PublicOutput retains root-parent read fds for two exact0600 files. Proposed
  child dup2 writers survive ID drop without making files user-readable. Parent
  closes its writers, waits for its exact direct child, checks exit, retained
  inode/parent entry/single-link/owner/mode/16KiB bound and fixed public payload.
  Deadline denies export and does not signal an identity-unstable PID. Own-child
  fork/pidfd lifecycle is still a future backend obligation. waitpid was mocked
  in local tests; no child/native tiny probe executed.
* Literal fixed Python argv and env are in SbfSeal-future-command.json. Postexec
  script checks saved/real/effective IDs/groups, capabilities/NNP, limits, exact
  FD survivors, null stdin and root-owned0600 output file types. FD enumeration
  closes listdir's inspection descriptor before fstat: only actual EBADF entries
  disappear. Surviving fd3 and high inherited FDs reject. No arbitrary fd3
  exception, no assumption lowering RLIMIT_NOFILE closes high descriptors.
  Single-threaded runtime/private proc are retained prerequisites; syscall/
  capability ABI, inherited socket closure, stdio inode join and exact process
  namespace/mount checks have NOT been established by these synthetic checks.

## Actual producer route and immutable assessment

SbfSeal_admission pins the actual f29c3e0e8c ResourceRssGO_host source digest.
The immutable source path is verify/inherited-limits -> outside collect
('prospective') -> policy.evaluate(additional4GiB) -> exact3G/4G/swap0/tasks64
systemd scope -> verify/controls -> collect('inside-scope') -> scope/self/control
crosschecks -> go_flow -> metadata marker. It has NO helper continuation.
ResourceRssGO_adapter loads the pinned ResourceStability evaluator and the actual
ResourceStat identity/scan functions; full source/dependency pins retained.
Neither the evaluator nor marker is adopted as launch authority.

Current authoritative manager assessment:468 failed before GO on Mac/Linux
RLIM_INFINITY; separate repair36049 pending and unread. Older f29 handoff
records a different earlier unstaged-import failure. Both retained, neither
provides new identity or fresh admission. No old receipt/unit/epoch/TTL reused.

project reads up to32MiB of the ACTUAL report schema (rather than old1MB limit),
rejects duplicate/nonfinite JSON, checks phase/count-once fields and collector/
inside binding, derives hash+size from EXACT full raw bytes plus immutable
producer pin. It explicitly returns authorized:false: full policy, count-once,
visibility and provenance are NOT recomputed by projection. Small synthetic
reports never imply actual GO or 16MiB production parsing has passed.

check_ancestry is an explicitly synthetic model for collector->sudo->helper or
collector->sudo->sudo-monitor->helper. It checks both complete observations,
PID/starttime/executable pins, actual parent chain, same cgroup, all saved IDs
and capability ABI; helper getppid need NOT equal original collector PID.
Observations must eventually come from actual HOST procfs, before namespaces.
Guest PID can never authorize host admission. Fresh actual producer gate raises
unconditionally; no caller boolean/callback can authorize it.

SCOPE_ARGV describes the future new-unit command with inner env-i; it names a
nonexistent separately reviewed SbfSeal_producer.py intentionally. It is not a
launcher and cannot be substituted into old marker source. Current producer's
seven-key pinned outer environment/XDG/DBus/runtime route must be preserved or
explicitly reviewed, including a strict env-i outer collector invocation. No
prospective/scope/helper launch is available in this package. Actual fresh
collector/sudo/helper process identities, full report -> pinned compact receipt
handoff, effective ancestor controls and raw report/receipt ownership remain
mandatory. No 55/7/2GiB policy, API adoption or resource cap change.

## Namespace and finite input limits

SbfSeal_boundary.ORDER retains all required host -> unshare mount/net/PID ->
fork/wait -> verify changed namespace -> private propagation -> finite copy/seal
-> RO view -> finite writable tmp -> private proc/minimal devices -> stdio/FD
closure -> fd chroot -> cap/groups/saved IDs/NNP drop -> verify -> fixed exec ->
postexec -> parent collection gates. linux_setup denies: descriptor-target mount
ABI, flags/topology, exact private proc/dev, close/chroot and capability drops
need independent Linux review/allocated measurement. No path-based mount fallback
or host exec, userNS/security service/global/port changes. Old uid_map EPERM is
retained without attributing it to macOS.

SbfSeal-input-map.json carries all428 immutable archive+index mappings/checksums,
394 distinct indices, current private manifest hash5cc3aadc...c276/6304167B.
No remote path was read. Complete19714-file mapping is unavailable locally, and
same-uid0700 is not immutable. Counts357/344 graph,178/174 workspace-unified root
reachability and371 observed source sets are reused, not independent root compile
units.305 conservative extras are not selected-build necessity. Candidate probe
manifest remains null. SDK suffix is solana-release/bin/platform-tools-sdk/sbf;
criterion target was never entered/copied. Required links need finite exact
release-manifest resolution; omission needs separate unreachability proof.
Loader/dlopen/stdlib/pyc/import closure remains partial.

Seven REAL immutable SbfResolve query2 trace lines are retained with raw trace
pin: shared CLONE_FILES, wait4, failed ENOENT, unfinished, resumed, loader cache,
pyc. Raw capture additionally lacks parser-required timestamps and close/dup/
fcntl coverage. The old strict subset is pinned and unchanged, not weakened to
accept them. Next trace deliverable: reviewed thread/shared-FD/wait/split-record
semantics plus exact negative-directory/runtime mapping and complete FD capture.
No trace/parser/effect/Cargo-ready PASS inferred.

## Validation and exact evidence

All source paths, full parent/setup textual AND AST diffs, immutable references,
package pins and future literal argv are in this directory. Source audit records
old/new complete call sets. This is worker source review, not independent lead
approval. No original test suite was rerun. Reused old39 synthetic checks and
8362 metadata checks are explicitly historical, not fresh identity gates.

Commands all `python3 -B tools/sbf-seal-20261025/SbfSeal_receipt.py <label>`:

| Label | Exit | Methods/checks | Wall s | Peak RSS B | Swap | Source |
| --- | --- | --- | --- | --- | --- | --- |
| SbfSeal-v1-review | 0 | packet only | .492097291 | 35438592 | 0 | 8a9c33dd39 |
| SbfSeal-v1-tests | 1 | 30;9 fixture errors | .098049750 | 32047104 | 0 | 8a9c33dd39 |
| SbfSeal-v2-tests | 0 | 30 | .072590750 | 32342016 | 0 | ad02be729e |
| SbfSeal-v2-review | 0 | refreshed source/argv packet | .503414833 | 35373056 | 0 | df6ac01292 |
| SbfSeal-v3-tests | 0 | 31 | .099721416 | 30769152 | 0 | df6ac01292 |
| SbfSeal-final-audit | 0 | 895 | .285036791 | 28180480 | 0 | df6ac01292 |
| SbfSeal-v4-root-tests | 0 | 1 focused mocked layout/root check | .057295459 | 32096256 | 0 | 8f60a287e9 |
| SbfSeal-v3-review | 0 | packet root/source refresh | .476937625 | 33914880 | 0 | 8f60a287e9 |
| SbfSeal-v2-final-audit | 0 | 895 | .345511875 | 30162944 | 0 | 8f60a287e9 |

Per-label receipts retain full exact argv, revision, tool/dependency/runtime
hashes, log hash, exit, wall, RSS, swaps and axioms=N/A. RSS is getrusage peak
through the target's completion before receipt hashing; wall includes receipt
preparation before final serialization. Module __file__ hashes/executable hashes
are observed local runtime inputs, NOT complete loader/bytecode/runtime closure.
All local work <512MiB; no Linux scope/limit enforcement claim. No derived JSON
>5MB committed. Private large manifest remains hash+size only. Failures, first
sources in8a9c33dd39 and superseded bounded-FD approach remain in Git/evidence.

Final cross-file consistency review corrected only the setup constants from
ROOT=owned-parent to OWN=owned-parent, ROOT=OWN+'/rootfs' (8f60a287e9). A new
focused mocked-layout check verifies actual planned creation sequence and root
mapping. Prior31-method ordinary/synthetic suite is reused for unchanged path/
output/FD logic; no unchanged full rerun. Packet and source audit refreshed for
this exact changed source. Full source/AST diff and history retain both variants.

Tests establish actual ordinary nofollow/exclusive/rename-replacement/hardlink/
source mutation/destination sealing/public-output bounds behavior. Metadata,
ancestry, wait, capabilities, GO schemas and FD inventories are explicitly mocked.
The audit895 is source/data consistency, not895 security obligations discharged.

## Before/after claims, trust and next gate

Before: old disabled helper has no actual authorized run; unsafe user-owned
ancestry/path writes, fd3 exception, uncollectable public output and blocked GO.
After: new disabled candidate has concrete fd-anchored construction/capture/
output collection and explicit unsupported kernel/producer boundaries, validated
only as above. No theorem statement/premise/quantifier, protocol/model/source/
parameter or security contract changed. No output-equivalence conclusion hidden
in a premise. No trust assumptions added or security assumption discharged.
Root ancestry, complete finite loader/runtime mapping, actual fresh admission,
Linux namespace/mount/drop/exec/FD lifecycle and coherent artifact joins RETAINED.

Next prerequisite: independent lead review of this packet, reviewed CURRENT fresh
producer continuation with strict outer env-i and actual host ancestry/receipt
binding, complete tiny-probe runtime manifest and reviewed fd-target Linux backend;
then SEPARATE explicit actual tiny-probe allocation. Editing an allowlist alone
cannot enable execution. No full frozen manifest authorization. Current ELF pins
unchanged/defaultf8c0ec72/devnet63ad3e9c/Pool121f3e29, not rebuilt or revalidated.
P7 compilation does not establish memory/effect rules. Any later heavy build must
use manager-reviewed optimized build-script override3, fresh generated table and
all3 exact ELF identity gates. Frozen4bb capture is not later prover adoption.
Kani59/60 and all formal budgets unchanged. BOTH DEPLOYED TARGETS NOT ESTABLISHED.
