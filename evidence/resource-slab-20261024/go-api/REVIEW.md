ResourceGO handoff — unadopted, management audit only

Established claim and API statement change

Before: resource_slab_candidate.propose(old, before, after, Q) requires Q>0
for every call. Therefore an existing capped scope already in finite frontier B
cannot request GO with Q=0; requesting its cap again would double count it.
That source and all previous evidence are retained byte-for-byte.

After: go_api.py, API ResourceGO-phase-v1, exposes read_only_admission with
keyword-only phase, additional_bytes, expected. It accepts no PID or scope path.
Prospective requires positive additional bytes and no existing-scope declaration.
Inside-scope requires exactly zero additional bytes and explicit expected high,
max, swap=0, tasks=64. Expected positive high<=6 GiB and high<=max<=8 GiB are
numerical adapter bounds, not authorization to launch or lower a cap. The actual
host-job policy remains 6G/8G or retained stricter existing 5G/7G, swap zero,
TasksMax=64. No consumer, reservation, scope or host mutation is implemented.

The adapter reads actual /proc/self/stat twice, status and cgroup, derives
os.getpid and exact unified membership, then repeats around each complete
unchanged hierarchy scan. PID/TGID/starttime must match enumerated scope
membership. It requires a populated, memory-enabled domain .scope with pids
delegation, exactly matching measured high/max/swap/tasks, no current swap,
and finite frontier coverage by that scope or a covering ancestor. Finite
ancestor high/max and task limits cannot be smaller than expected. Two scope
bindings and existing hierarchy/membership/control comparisons must agree.
Missing/unreadable observations, identity migration, wrong caps, unknown phase,
zero prospective, positive GO and outside qualifying scope deny. Successful
bindings record expected/observed controls, identity, frontier and ancestors.
Denied live observations retain all measured controls in returned snapshots;
the offline coverage summary also exposes the collector's observed limits.

Pure evaluate(old,before,after,Q,phase,expected) is offline replay of supplied
observations, not live provenance. Synthetic snapshots cannot authorize a live
GO. read_only_admission collects its own live inputs using unchanged legacy
helpers. No conclusion of output equivalence or guaranteed admission is hidden
in a premise. The new obligation is concrete identity/control/frontier binding;
all former visibility/accounting obligations remain, with no new trust axiom.

Retained accounting and historical evidence

The estimate is still B+Q+max(raw root residual)+sum(max exclusive current minus
min inactive-file credit minus min half exclusive slab credit)+7 GiB. No credit
inside the finite frontier, no root residual credit, no active-file credit.
Memory-disabled and threaded subtrees remain charged at their memory owner.
Strict B+Q<55 GiB, MemAvailable>Q+2 GiB, physical-total inequality, legacy
visibility/errors and cap denials remain mandatory. Own admitted scope is in B;
GO adds zero. Half exclusive slab remains an estimate, not guaranteed reclaim.

The earlier threaded 116-node/1,308-TID capture and 40-test receipts are unchanged
point-in-time evidence. Its 4 GiB proposal had 114,380,240 bytes (~109 MiB) EXTRA
margin above the explicit 7 GiB control reserve and retained half slab/active
file; it was neither actual free RAM nor a zero-OS-headroom or physical reclaim
guarantee. Old background-list omissions (including 22 empty charged groups)
and fully charged raw root residual remain explicit. Old failed reads,
portability tests and reviews are preserved, never retroactively repaired.

Both legacy source files still match f033f68bf7 byte-for-byte; audit receipts
record SHA-256/size. Primary kernel/API source assessment from parent evidence
is reused unchanged, not newly fetched, and not an ELF/source identity gate.
Current default/devnet/Pool ELF pins were not rebuilt or tested. No crates,
programs, formal source, shipped gate, protocol, wire, feature, trust/security
contract, key or old consumer was changed. No compiler/build/Lean/Kani/extraction,
ELF or consumer ran; no scope/reservation/lock/cache/service was created.

New validation and physically observed blocker

57 synthetic tests pass: all 40 existing adversarial tests plus 17 GO/API/
collector tests. Exact command: python3 -B -m unittest discover -s
 tools/resource-slab-20261024 -p 'test_*.py' -v. tests.json/log retain exit 0,
wall 0.205770666 s, child peak RSS 32,735,232 bytes, swaps 0, HEAD 07e51d8145,
and exact source/dependency hashes matching the final host-tested operational
files. Source was committed as 07e51d8145 then collector correction f88cae2c12.
GO successes are mock-proc/snapshot tests only: expected high6/max8/swap0/tasks64;
8 GiB own frontier counted once, or 12 GiB covering frontier once. There has
been no real inside-capped-scope GO or consumer validation. Prospective 4 GiB
adds its full cap in the synthetic test; zero prospective/positive GO deny.

The ONLY new host diagnostic used source f88cae2c12 at 2026-10-24T20:34:44Z.
Exact SSH argv and source/stdin hashes are in live-command.json, full stdin in
live-stdin.py.txt. Exit 0 (collection, not admission), SSH wall 28.610519792 s,
local child peak RSS 6,471,680 bytes, swaps 0. Host collector wall 0.932466615 s,
self peak RSS 33,616 KiB, swaps 0; aggregate host/children RSS and swap N/A.
Read-only metadata was streamed over stdin with no remote writes/scopes or
reservation. No host job/build was launched. No cap was raised and no unchanged
resource failure was rerun. Interpreter/stdlib binaries were not hashed;
operational Python sources/dependencies and all observed raw inputs are hashed.

Both snapshots enumerated 116 nodes, 1,313 TIDs, 306 root direct processes,
101 domain / 2 domain-threaded / 12 threaded non-root nodes. Ordered read logs
contain 6,876 events per hierarchy scan and 5,434 successful unique paths;
14 recorded expected errors per scan are the two root cgroup.type ENOENT reads
and twelve threaded cgroup.procs errno95 reads. Legacy recorded 835 read/command
events, 39 commands, 735 successful paths; 438 process rows plus header,
40 service rows and 18 Docker observations. All inputs and repeated reads are
retained, including the 22 empty charged groups and root residual.

The exact self PID 3650646 / starttime 21302738 belonged to the real SSH
session-53416.scope in both scans. This is a populated memory-enabled session
scope, but high/max/swap/tasks controls were all unlimited (null). GO with the
explicit expected 6G/8G/0/64 correctly denies: actual controls differ. The actual
scope and its membership were never replaced, excluded, or double-counted.
Expected/observed limits and self identity are in coverage-summary.json and raw
snapshots. No inside authorized capped-job-scope admission was physically seen.

Hierarchy/membership/control identity matches across the observed pair, and the
before snapshot passes accounting. AFTER accounting FAILS at
system.slice/hausklar-fitness-worker.service: measured exclusive current
12,107,776 bytes, while inactive_file+active_file+anon+kernel = 12,111,872 bytes,
a 4,096-byte excess. Complete raw fields are in coverage-summary.json and
input shards. No unproved explanation, rounding tolerance or retry is used.
All prospective 1/2/3/4/6/7/8 GiB decisions deny that inconsistency; their current
estimate/physical-margin/headroom is UNKNOWN, not the earlier 109 MiB margin.
All corresponding legacy positive requests also deny the physical reserve.

The observed finite frontier remains 26,172,456,960 bytes (24.375 GiB), below
strict 55 GiB. Minimum observed MemAvailable=55,792,009,216 bytes and physical
total=66,698,661,888 bytes do not override the failed consistency gate.
Raw root residuals 2,247,208,960 / 2,240,557,056 bytes remain fully charged in
the proposed rule; no credit or valid pair envelope is computed from this pair.
The explicit 7 GiB OS/control reserve and retained half slab/active file remain.
Offline audit, failures and disposition

python3 -B tools/resource-slab-20261024/audit_go.py reconstructs both complete
scans from every ordered read, mocked hierarchy directory inventory and exact
recorded errnos. It independently checks raw-input shard and event SHA-256,
replays both self observations, confirms process membership/control agreement,
recomputes every prospective/GO decision exactly, and retains the accounting
failure instead of asserting a successful reserve estimate. Exit 0 means the
audit reproduced the recorded denials. Final audit-receipt.json records wall
0.528533625 s, self RSS 67,076,096 bytes, swap0, revision f88cae2c12 plus exact
new audit source/dependency/input hashes. audit.time additionally retains full
external /usr/bin/time -l output. Adding explicit observed collector controls
justified the final offline audit rerun; intermediate audit receipts are kept.
No further host read was performed.

Preserved new failures: failed-fixture-tests (54 tests, missing-control fixture
called legacy accounting before exercising evaluate); failed-retention-tests
(54 tests, migration failure recorder assumed mock snapshot read_attempts);
failed-collector-preflight (NameError before SSH); failed-audit-self-reads (raw
proc status/stat content comparison instead of stable identity). Replacements
fix the fixtures, retain every failed read, use pathlib.Path, and compare stable
identity while separately hashing/replaying every raw value. Intermediate green
test/audit receipts remain. The uninstrumented collector/audit preflight failure
receipts explicitly say wall/RSS/swap N/A; enclosing tool wall is not relabelled
as exact process telemetry. These failures were not resource failures or host
admissions. Operational go_api/collector bytes have not changed since the single
host capture. Finalizer manifest hashes every retained file; no JSON >5 MB or
binary is included. #print axioms is N/A throughout; formal budget ZERO.

Recommendation: lead review the phase adapter and synthetic count-once evidence;
do not adopt or launch on this capture. Current useful blocker is the observed
4 KiB accounting inconsistency, not a permission to weaken it or retry unchanged.
Future real GO requires lead adoption and an independently reviewed consumer
inside its actual authorized capped scope, fresh complete consistent measurements
and all retained inequalities. There is no atomic/future visibility or physical
reclaim guarantee. No security premise was discharged or added; resource API
bookkeeping alone closes no native or cryptographic theorem. Both security
targets remain not yet established.
