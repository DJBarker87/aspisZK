ResourceSLAB review — 2026-10-24 — UNADOPTED; recommend no adoption

Scope and established claim

This branch implements an isolated Python resource-estimate candidate and focused
synthetic tests. No shipped code, formal source, protocol, security contract,
ELF, worker gate, host service, scope, cap, cache, or wallet was changed. No
compiler, Lean, Kani, extraction, arithmetic, build, or consumer ran. Formal
budget is ZERO; #print axioms is N/A. Both security targets remain not established;
no native or cryptographic obligation was closed. There are no new trust
assumptions. No permission to adopt or launch is implied by an `allowed` field.

Immutable baseline

The two legacy helpers were recovered byte-for-byte ONLY with `git show
f033f68bf7:tools/prover-rw-20261023/resume-roles/{reservation.py,reservation_base.py}`.
Their hashes, sizes and explicit reuse assessment are in
`immutable-source-assessment.json`. Historical scanner source is reused, not a
new artifact identity gate. Current ELF pins are unchanged and were not tested.
The helper directory is job-prefixed; immutable filenames are retained so the
original relative run_path dependency resolves without modifying either file.

Before and proposed after

Let B be the sum of populated finite MemoryMax values at the outermost finite
frontier, Q the requested cap, I the exclusive inactive_file bytes and S the
exclusive slab_reclaimable bytes. Descendants of each finite frontier node
are charged through that ancestor's whole cap exactly once.

Before: only populated uncapped, uncovered memory-controller groups contribute
C-I. Root direct usage and unpopulated-but-charged groups are omitted. Tests and
inspection establish those omissions; the live old snapshot contains 22 empty
groups with positive current (listed, without assuming their hierarchical
currents can be summed, in coverage-audit.json).

Proposed after: every uncovered enabled accounting node, populated or empty,
finite or uncapped, contributes C-I-floor(S/2), using direct enabled-child
subtraction for every component. No credit applies inside the finite frontier.
No active-file credit is introduced. All remaining anonymous, VM, kernel and
unreclaimable usage is retained through current, not an incomplete component
sum. Disabled-memory subtrees remain included at their nearest accounting owner;
they are inventoried and not interpreted as zero usage.

Because root has no memory.current, the candidate retains in full the residual
MemTotal-MemFree minus top accounting-node hierarchical current. This covers
root direct processes and globally uncharged memory, with no residual cache or
slab credit. Negative residuals or inconsistent components deny. This can be
substantially more conservative than the lead's half-slab-only proposal.

Two complete snapshots must agree on hierarchy, membership and limits. Each
must pass unsigned/overflow, parent-child current/stat, population, component
nonoverlap and finite-current-versus-cap checks. For each uncovered cell the
estimate uses max(current) and min(each credit) across the snapshots, plus the
larger root residual. This is a conservative snapshot envelope, not atomicity,
a lock, future admission, or proof of physical reclaimability. Inconsistent
snapshots, missing fields and unknown visibility deny.

Both rules retain strict B+Q <55 GiB, a 7 GiB OS/control reserve, and
MemAvailable >Q+2 GiB. Projected cap and visibility denials in the legacy result
cannot be overridden. Only its physical-reserve denial is eligible for a changed
proposal estimate. The old result, fields and decisions are retained. Consumer
scope limits are descriptive only: 6G/8G, swap 0, tasks 64, or existing stricter
5G/7G, remain unchanged; no scope is created or validated. Hypothetical Q must
match an eventual independently reviewed actual cap. These diagnostics do not
authorize Kani 3/4 GiB or Lean 7 GiB consumers, nor lowering anybody's cap.

Reference assessment

The kernel documentation describes slab_reclaimable as potentially reclaimable,
not guaranteed. Linux v6.8's si_mem_available adds reclaimable kernel memory
minus the smaller of half that amount and the low watermark. The candidate
credits only half of exclusive slab_reclaimable, rather than reproducing that
whole-host kernel calculation or crediting all reclaimable kernel memory.
This is an estimate with explicit risk, not a kernel guarantee.

Primary sources (hash/size receipts in primary-references.json; no GPL excerpt
redistributed):
https://docs.kernel.org/admin-guide/cgroup-v2.html
https://github.com/torvalds/linux/blob/v6.8/mm/show_mem.c

New validation and retained failures

28 focused tests pass. tests.json records exact command, exit, wall, peak RSS,
swaps, revision and source/dependency hashes; tests.log retains full output.
Tests exercise finite ancestor once, siblings and ancestor constraints,
exclusive accounting, empty finite/uncapped charged groups, disabled ownership,
missing memory.stat/slab fields, negative/overflow values, nonoverlap, strict
55 GiB/available/physical boundaries, root residual, membership/control races,
and unsupported reads. These are synthetic tests, not a physical-reclaim proof.

There was one preliminary uncapped READONLY SSH inventory command before tests:
`ssh -o BatchMode=yes -o ConnectTimeout=10 dombarker@100.108.41.90 'uname -r; cat /proc/meminfo; cat /sys/fs/cgroup/cgroup.procs'`.
It exited 0 in 0.934470125 s; RSS/swaps N/A (not instrumented), no admission
computed, no persisted input receipt, and its output is not reused as validation.
This was earlier than the requested diagnostic cadence; no build or allocation
was involved. The complete diagnostic attempts below occurred after tests.

The first full diagnostic failed because memory delegation does not imply pids
controller delegation: pids.max was absent in libvirt. Failure command, exact
stdin source, hashes, resource receipt, null snapshots and denied results are
retained in failed-pids-assumption/. Its partial inputs were not captured by
that version; do not treat it as coverage evidence. The source was changed to
track parent pids delegation explicitly (no whitelist); missing pids.max still
denies when pids is delegated. This new scanner case was tested before the
source-changed diagnostic; no unchanged resource failure was rerun.

The second diagnostic ran at 2026-10-24T19:58:43Z on 6.8.0-147-generic. Legacy
visibility succeeded: 116 hierarchy nodes, 435 process rows, 40 running service
rows, 18 Docker states/configurations. Populated finite reservations were
26,172,456,960 B, below 55 GiB. All hypothetical legacy 1/2/3/4/6/7/8 GiB requests
denied the physical-reserve inequality; available-memory and cap checks passed.
Those request variants are algebraic reevaluations of ONE measured old snapshot.

The candidate scan failed reading cgroup.procs after reading subtree_control in
machine.slice's libvirt/emulator subtree. Linux documents EOPNOTSUPP for reading
cgroup.procs in threaded cgroups; that is consistent with the observed errno 95.
The exact cgroup.type was not captured, so threading is an inference, not a new
observed fact. The program does NOT catch-and-ignore this error or grant credit.
All proposed request sizes deny: incomplete before/after hierarchy snapshots.
No numerical new credit, new total, complete new coverage or changed live
membership has been established. legacy-snapshot.json, decision-*.json,
live-command.json and live-summary.json preserve exact old/new decisions.
failed-input-*.json retains every successfully read candidate input and its
SHA-256 before the error. No new source is claimed to have a completed live scan. A subsequent local-only
review tightened legacy visibility/decision type validation (None is unknown,
not a successful visibility read); focused tests passed. That stricter final
source has not been rerun on the host, and cannot repair the recorded blocker.

The host Python diagnostic took 0.603686234 s, self peak RSS 18,128 KiB, self
swaps 0, process exit 0 (collection completed; candidate admission denied).
RSS is the collector's self peak, not aggregate child RSS; child/aggregate peak
and swaps are N/A. SSH transport wall/resource data and source revision
 d3ac190cdf are in live-command.json. Host access was stdin-only Python and
read-only commands: no files, probes, scopes, lock or cache writes on the host.
JSON files are below 5 MB; the exporter records only hash+size for oversized
JSON and splits raw source interfaces for retention. No binaries are included.

Blocker and next deliverable

Do not adopt. Full candidate hierarchy/process coverage is not established on
this host. A next source change should model domain/threaded ownership using
cgroup.type and cgroup.threads (retaining domain process visibility), add
adversarial hierarchy tests, and obtain a complete independently reviewed
read-only snapshot. Do not special-case service names or silently ignore an
unsupported read. Subsequent admission still needs lead review and whatever
consumer prompt authorizes its exact independently capped scope. Half-slab
reclaim remains a resource estimate, never a physical or security guarantee.
