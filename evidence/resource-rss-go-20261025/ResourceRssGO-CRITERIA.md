# ResourceRssGO criteria and design, before implementation

Entry 4f4b0a2470, assigned branch codex/cx-resource-rss-go-20261025.
Only tools/resource-rss-go-20261025 and evidence/resource-rss-go-20261025.
Read AGENTS.md and both supplied common/local rules completely. Current manager
allocation supersedes historical coordination and pins. No other live worktrees,
logs, caches, keys, compiler/proof/backend/consumer/ELF/RPC operations.

Thin source derivation from immutable ResourceStableGO at 4f4b0a2470. Remove
import-time RLIMIT_AS lowering; never set AS/DATA or raise inherited limits.
Record initial limits, reject unexpected finite inherited AS/DATA, compare fresh
run limits with inspection pins. Preserve exact ResourceStability policy and
scanner/collector/unit/ancestor gates, seven-key inner env-i, child 15s timeout,
overall 115s metadata deadline, sealed sources, ordered record/replay and denial
flows. Historical policy/source/test evidence is reused, not newly certified.

A persistent thread starts before pinning/collection and survives both snapshots
and all child execution until final receipt. It uses direct proc reads (no helper
subprocesses), walks all task children, deduplicates TGID, pins PID/starttime,
checks live unknown children fail closed, tolerates confirmed disappeared children,
and records bounded sample/lineage/error details. RSS pages, not VSize or thread
RSS sums, count against 512MiB. Sampling is explicitly not continuous enforcement.
On failure, only verified owned descendants may be cancelled using pidfds; never
signal unrelated/reused identities. Thread creation must not occur during scans.
Scope remains High3G/Max4G/Swap0/Tasks64; authoritative cgroup peak retained.
This metadata guard must not be attached to a future native consumer.

New tests: synthetic large VSize/small RSS, aggregate breach, reuse/unknown child,
disappearance, safe cancellation and lifecycle; tiny Python child only; inherited
limits unchanged and no setrlimit; literal env/source/unit/control/deny gates.
No unchanged broad suites. Retain failures. Code/tests/seals committed BEFORE
host operations. At most one new epoch, charged before first SSH (even failure),
fixed Q4GiB prospective then at most one scope/GO and tiny marker only if allowed.
New own stage0700 and exclusive sentinels. Full independent ps/systemctl/Docker
visibility and full reservations below55GiB, OS7GiB/available2GiB gates unchanged.
No scope on prospective DENY; no marker on GO DENY. No retry/search/cap raise.
Capture/replay all new ordered inputs and exact reports, pins/env/controls/marker;
raw JSON >5MB hash+size with meaningful complete ordered shards. Record commands,
exit/wall/process sampled RSS/cgroup peak/swap/revision/hashes; unmeasured N/A.
Axioms N/A. Old three epochs remain charged: env UNKNOWN, TID race, Docker
page-summary reservation failure. AS inheritance is likely explanation, not an
exclusive-causality or Docker-version identity claim. Both security targets not
established. Kani59/60 RESERVED, other build/proof budgets0. No merge/push.

Next consumer requires separate review, allocation, fresh prospective and GO;
this bounded rehearsal gives no general adoption or native permission.
