ResourceTHREADS handoff — UNADOPTED; recommend do not adopt

Exact established claim and limits

Source 263e06712f03f2a1e5eac28bd91f4599e6b47eeb completed ONE read-only host
capture at 2026-10-24T20:12:58Z (kernel 6.8.0-147-generic). Both observations
contain 116 hierarchy nodes and 1,308 distinct TIDs, matched TID/TGID/starttime,
unified memberships, domain process sets, pids counts, hierarchy and controls.
The non-root observed types are 101 domain, 2 domain threaded and 12 threaded.
Root cgroup.type actually returned ENOENT (recorded), selecting the documented
special root case, not a guessed public type tag. All 12 threaded procs reads
returned errno 95; their thread identities, domain process visibility and
memory-owner checks completed. Root direct membership includes 301 processes.
No unknown live-data error was ignored. This closes the prior concrete API
coverage blocker for this observed pair, not an atomic/future visibility theorem.

Before/after interface change is recorded in ACCEPTANCE.md. The former universal
procs-read requirement is replaced only for an observed threaded node with its
complete alternate membership and ownership checks. No output/admission claim
is hidden in that premise. Domain and memory owners are distinct; independently
delegated pids controls remain read with memory disabled. INTERFACES.md lists the
complete read surface and retained observational assumptions. Raw ordered reads
include repeated values, hashes and errno; directory hierarchy is in snapshots.
The offline audit checks these hashes, exact two-snapshot membership, accounting
and every recorded proposal decision. No new trust assumption is introduced.

Old and new measured decisions

The unchanged legacy helper newly observed 116 nodes, 431 process rows plus a
header, 40 running service rows and 18 Docker State/HostConfig observations.
It still omits 22 empty charged groups and root residual. Historical legacy
source is reused with its prior explicit source assessment, not a new identity
gate. The new run does not reuse old live inputs or revise old denials.

All byte values below are in coverage-summary.json. Reservations: 26,172,456,960
B (24.375 GiB), below the unchanged strict 55 GiB threshold. Raw root residual:
2,259,865,600 B before, 2,262,740,992 B after; fully charged. The conservative
per-cell envelope credits 6,480,477,648 B half exclusive slab and 21,275,926,528 B
inactive file, leaving 26,337,923,632 B uncovered reserve. The legacy uncapped
resident estimate was 32,800,722,944 B. No root credit or zeroing of disabled
threaded subtrees occurs. Active file, anon, unreclaimable kernel and VM usage
remain retained through current; caps, 7 GiB control reserve, strict finite
<55 GiB and MemAvailable > request+2 GiB checks are unchanged.

Request GiB | Legacy allowed | Proposal allowed | Proposal total B
1 | false | true  | 63,363,056,176
2 | false | true  | 64,436,798,000
3 | false | true  | 65,510,539,824
4 | false | true  | 66,584,281,648
6 | false | false | 68,731,765,296
7 | false | false | 69,805,507,120
8 | false | false | 70,879,248,944

Physical total is 66,698,661,888 B. The 4 GiB estimate has only 114,380,240 B
(about 109 MiB) margin. Every legacy denial is physical reserve, with caps and
available tests passing; the new 6/7/8 GiB denials are also physical reserve.
Variants are algebraic decisions on one legacy observation and one paired
candidate capture, not seven host replays. Root residual is not dominant here
and does not make all requests deny. No root credit proposal is implemented
or needed to explain these results. Half slab remains an estimate of potential
reclaim, not guaranteed reclaimability, reserved memory or launch authority.

Validation, provenance and retained failures

40 focused synthetic tests pass, including the original 28 boundaries and
12 threaded/collector cases. Exact command is in tests.json, exit 0, wall
0.253426750 s, child peak RSS 31,834,112 B, swaps 0. Receipt HEAD was 06cad62aec
with source hashes that exactly match the subsequently committed 263e06712f
operational files. The 8-error portability attempt (39 tests, macOS EOPNOTSUPP
constant versus Linux 95) is retained in failed-portability-tests.*. All original
28-test receipts, old source inputs, failures and historical reviews are intact.

Host command is `ssh -o BatchMode=yes -o ConnectTimeout=10
 dombarker@100.108.41.90 'python3 -B -'` with exact stdin in live-stdin.py.txt
and SHA-256 in live-command.json. Exit 0, SSH wall 22.937471292 s, local child
peak RSS 6,160,384 B, swaps 0. Host collection wall 0.975212348 s, self peak RSS
34,496 KiB, swaps 0; aggregate/child host peak and swaps N/A (not measured).
No host scope/reservation was created; read-only metadata only. Host interpreter
version/stdlib binary hashes were not captured; source/helper dependencies and
all actual read inputs are hashed. No binary/artifact identity claim follows.

Offline audit command: `python3 -B tools/resource-slab-20261024/audit_threaded.py`,
exit 0, wall 0.106650000 s, self RSS 41,549,824 B, swaps 0. audit-receipt.json
records its own source hash, interpreter and dependencies; this additional tool
runs locally only. The candidate and collector themselves have NOT changed
since the host-tested 263e06712f. Final evidence-only commit retains those exact
operational bytes. No local-only candidate fix is reported as a live pass.

Primary API reference is hashed in primary-reference.json; prior immutable
helper/half-slab source assessments are explicitly reused. artifact-hashes.json
records all final retained files (excluding itself). No JSON exceeds 5 MB; no
binaries or objects are committed. #print axioms: N/A throughout, formal budget
ZERO. No Lean/Kani/Rust/extraction/backend/ELF/consumer/scopereservation job ran.
No host files, caches, services, scopes, keys or worker gates changed. No merge,
push, adoption or permission for a launch is implied by any `allowed` field.

Next deliverable

Do not adopt: the concrete collection blocker is resolved, but the half-slab
reclaim estimate and admission use still need independent lead review and an
explicitly authorized consumer producer with its own current gates and cap.
The narrow 4 GiB margin particularly precludes interpreting this observation
as a future admission. All original resource controls remain authoritative.
Both security targets remain not established; this management diagnostic closes
no cryptographic or native theorem. No frozen-manifest or final Kani gate ran.
