# One actual ordinary-user DATA action

Allocation: current lead instruction of 2026-10-25, source review at
7717cea25278a59bd047fec3c4e34f00822ab43b. This supersedes the source-only
release notice solely for this one invocation. No final producer authority.

PRE-LAUNCH EXCLUSIVE CHARGE: main SSH DATA action 1/1 is consumed before
launch, including connection/parse/spawn uncertainty. No retry. The run helper
records the new action revision after this criteria/charge commit. Historical
source/job revisions inside the reviewed payload are provenance, not a new
identity gate. The initial preflight revision is the reviewed source revision.

Exact local command:
`python3 -B tools/prover-rw-20261023/final-native-gate/prospective-data-v3/FinalNativeGate-data-transport.py`

Exact sole main SSH argv:
`/usr/bin/ssh -T -oBatchMode=yes -oConnectTimeout=10 -oStrictHostKeyChecking=yes -oClearAllForwardings=yes -oForwardAgent=no dombarker@100.108.41.90 '/usr/bin/python3 -I -B -'`
Stdin is the exact receiver. No preflight SSH, fallback, extra upload or remote
command. Local source hashes and decoded payload compared without importing it.
All 44 maintained source pins and 44 payload pins must match release identities;
all v3 file hashes are retained. Receiver/root must equal the lead review pins.
Target ELF pins retained (not rebuilt or newly checked on host): default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Acceptance/interpretation criteria:
- New exclusive 0700 fixed leaf only; exact 44 payload files, <=16MiB;
  no overwrite/adoption/cleanup. Retain all partial paths and all outputs.
- Reviewed prospective admission: full fresh 1GiB, populated reservations
  strictly below55GiB with reserve7GiB/guard2GiB and both raw visibility scans.
  Admission denial means no scoped workload and no retry.
- Actual fixed FinalNativeGate-pin-setup.scope: MemoryHigh768MiB,
  MemoryMax1GiB, MemorySwapMax0, TasksMax64; inside resident512MiB/115s;
  outer120s and combined public output4MiB. No cap change or heavy operation.
- Inspect every returned summary record before selecting any followup. Verify
  transfer root/count/bytes and available report identities against source.
  Missing record, non-JSON, setup exit/error, stale pin, 4KiB collector or
  permission error is a retained failure, never a default GO.
- SSH exit alone is not remote closure. Evaluate actual setup_exit, parent
  errors/unresolved state, source scope cleanup/guard receipts; failed:false
  alone is insufficient because it precedes receipt-write attempts.
  cgroup.kill metadata is not kernel write viability or D-state termination.
- Exactly one conditional read-only systemctl show is permitted only for primary
  timeout/disconnection/missing terminal/unresolved scope, charged separately
  before its call. Exact lead-specified env/strict SSH/metadata properties;
  <=20s/4MiB locally, no second poll or remote process kill.
- Candidate roles UNRESOLVED remains DATA. Seven FINAL fields remain NULL;
  no pin/plan/cache promotion, native semantics or security closure claim.

Evidence retains argv, revision, source/dependency/runtime hashes, UTC,
exit/wall/RSS/swap, raw stdout/stderr and receipt. Local helper samples aggregate
own process tree RSS; no unrelated worktree/cache/log access. Axioms=N/A: data,
no theorem. Derived JSON >5MB stays external with hash+size only in Git.

Reused validation: lead reports independent v3 source/release review and
8 ordering +14 receiver +6 activation/receipt tests, 49-artifact byte-identical
reproduction, receipt /private/tmp/lead-final-native-data-v3-review-20261025-v1/receipt.json.
That historical review is not rerun or relabeled as this action's validation.
New validation is local byte identity plus the one actual DATA action only.

Counters retained: final Kani59/60 reserved; Lean240/260; extraction54/56;
backend15/16; Rust2/3 (this ordinary DATA allocation1); ELF0/3. Soundness365/368
(2reserved+1carry). Actual heavy/proof/nativebackend/root/compiler/cargo/Kani/
Lean/extraction/ELF all0. Main SSH1 plus conditional0 or1 will be reported.
OS/systemd/procfs/Python/bootstrap/compiler/Kani/policy trust unchanged;
no premise changes or theorem assumptions discharged. Both deployed security
targets NOT ESTABLISHED. Stop for lead review; no final Kani or further host job.
