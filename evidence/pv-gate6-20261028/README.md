# D350 merged candidate adoption gate

## D358 resumed Stage B: UNDECIDED

Exactly one new window; 10/10 pairs completed, 10 valid, 0 invalid, 10 throttled, **0/10 valid and unthrottled**. The D358 gate requires the full planned count of ten valid, unthrottled pairs. The first window’s seven throttled pairs remain separate historical evidence.

Window marker written **2026-10-28T08:09:40.891658+00:00**, immutable expiry 2026-10-28T08:34:40.891658+00:00. Measurement **2026-10-28T08:09:41.209839+00:00–2026-10-28T08:18:55.157937+00:00**. Marker removed **2026-10-28T08:18:55.158023+00:00**, 0.000087s after measurement ended. Drain 0.040628s. No marker extension. Immediate deletion is recorded in `measurement-marker-removal.json`; the subsequent fallback trap found it already absent.

| Fixture / sample | n | Candidate median (p10–p90), s | Control median (p10–p90), s | Candidate/control |
|---|---:|---:|---:|---:|
| transfer / all | 10 | 13.890624 (13.333722–14.102306) | 13.917514 (13.399391–14.305008) | 0.998068 |
| transfer / valid_unthrottled | 0 | unavailable | unavailable | unavailable |
| transfer / valid_throttled | 10 | 13.890624 (13.333722–14.102306) | 13.917514 (13.399391–14.305008) | 0.998068 |
| transfer / invalid | 0 | unavailable | unavailable | unavailable |
| withdrawal / all | 10 | 13.904879 (13.270859–14.091145) | 13.846374 (13.235030–13.995137) | 1.004225 |
| withdrawal / valid_unthrottled | 0 | unavailable | unavailable | unavailable |
| withdrawal / valid_throttled | 10 | 13.904879 (13.270859–14.091145) | 13.846374 (13.235030–13.995137) | 1.004225 |
| withdrawal / invalid | 0 | unavailable | unavailable | unavailable |

Per-pair thermal telemetry (maximum package temperature, and maximum per-CPU counter increment; package counters may be repeated across CPUs):

| Pair (coin) | Package °C before → after | Package throttle count Δ | Core throttle count Δ | Valid |
|---|---:|---:|---:|---|
| 1 (100) | 87.0 → 87.0 | 28591 | 16376 | True |
| 2 (101) | 87.0 → 94.0 | 49720 | 25067 | True |
| 3 (102) | 94.0 → 84.0 | 49944 | 25080 | True |
| 4 (103) | 84.0 → 91.0 | 48385 | 24344 | True |
| 5 (104) | 91.0 → 86.0 | 43785 | 22014 | True |
| 6 (105) | 86.0 → 99.0 | 43960 | 22052 | True |
| 7 (106) | 99.0 → 88.0 | 47269 | 23743 | True |
| 8 (107) | 88.0 → 102.0 | 42394 | 21303 | True |
| 9 (108) | 102.0 → 89.0 | 41226 | 20691 | True |
| 10 (109) | 89.0 → 90.0 | 41687 | 20917 | True |

Transfer: **UNDECIDED**. Withdrawal: **UNDECIDED**. Throttled or invalid pairs do not supply a gate verdict. Stop reason: planned measurement complete. No additional window launched.

Shared reservation.py verified before the marker: `662a42781e004635a4a0bde760a90082834834aa63bb15a3062ea0aef490542d` (lead’s D358 repair, candidate 508dfb9230). Optimized binary hashes rechecked: control `1975a5d1bbdf3ca3378bd3b905f6f387862937bf019321f6f3d315c9b2cdfea6`, candidate `1ee2411fadb901fa14420c9bdf719012e3012836993e7af26a3d8a1f9eb92dc7`. Both match retained build pins; no rebuild, compilation, Lean or Kani. Stage A PASS on 82566acdfb is reused unchanged, including three ELF pins, pinned client, fixed fixtures and 1,000/1,000 differential.

Each pair alternates control/candidate order, pins CPU affinity to 0–21, and records package temperature and throttle counters before/after. Running cx-/pv- scopes and every other capped user job are inventoried before each pair and each side, and after each side (50 retained snapshots); any intrusion marks the pair INVALID, with stopping only after three consecutive invalid pairs. Proof/public bytes, canonical results (seconds excluded) and ledger files match within every completed pair on both fixtures.

New measurement scope receipt: exit 0, wall 553.984s, peak RSS 696048KiB, swaps 0, cgroup peak 744050688 bytes; MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; candidate revision 82566acdfb488183022f41ac564c11df22c9404f; #print axioms N/A (native measurement). Full receipts, telemetry, guard inventories, transport retries and independent statistics validation: `resume-d358/`.

No Cargo targets were created; previous task-target cleanup stands. No key cleanup or movement; keys and raw proof evidence remain securely on the host. Premises before/after unchanged: removed0, retained substantive obligations, added0, weakened0, changed0. T remains entropy_law, entropy_kernel, observation. Target not yet established. Next deliverable: lead review of the thermal evidence and a separately authorized way to obtain the full valid, unthrottled cohort.

---

The report below records Stage A and the original D350 window; its partial timing verdict is historical.

Candidate `82566acdfb488183022f41ac564c11df22c9404f`, branch `codex/pv-gate6-20261028`, exact worktree `/Users/dominic/ZK/.worktrees/pv-gate6`. Host directory `/home/dombarker/project-offloads/codex-pv-gate6-20261028/`.

Stage A: fresh default/devnet/Pool ELF rebuild and pin comparison; pinned 1.94.1 devnet_spend client; fixed coin0 against retained SHA-checked 37e5e133f8 control; fresh seeds6000–6999 whole-prover differential against c57a344726 using pv-integ4's harness, comparator, concurrency and scope recipe. D328 criterion compares proof, public, ledger and canonical result bytes, excluding elapsed seconds only.

Stage B is conditional on Stage A PASS. Ten alternating paired fresh processes per side, coins100–109 (minimum five unthrottled pairs), fixed CPU affinity, both transfer and withdrawal per process. Record package temperature and throttle counters before and after each pair, separate throttled pairs. Gate per fixture: candidate median strictly below15s, ratio of candidate/control medians at most1.10. Quiet marker must be written before drain, last at most1500s, never extended; drain at most600s. Trap removes own marker immediately when measurement ends or process exits. Partial receipts retained on expiry.

No implementation source change, Lean or Kani. All native workloads use serial capped host scopes: MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64; optimized Rust -j4. Admission requires allowed:true and exit0. Resource refusal waits180s, maximum10 retries. Source exports are checked against exact git blobs. No binaries, keys or raw proof bytes committed. Only task-owned Cargo targets will be removed.

This is finite artifact, functional and timing validation. Premises before/after unchanged: removed0, added0, weakened0, changed0. T remains entropy_law, entropy_kernel, observation. Source-to-model/deployed endpoint closure, E1/E2, real RunJoin, entropy/kernel bridge, OS-failure independence, inversion boundary, client proof-account adoption and L1/L2/L3 retain their substantive proof and deployment obligations. Target not yet established.

## Stage A results: PASS

All three freshly rebuilt ELF pins match. Default47.223s/684472KiB RSS, devnet33.067s/687096KiB, Pool55.832s/676608KiB, all exit0/swap0. Client build140.266s/640276KiB, rustc1.94.1(e408947bfd200af42db322daf0fadfe7e26d3bd1), LLVM21.1.8. Client SHA256 `0d9dbd91d4eb9b4add14e164f8ffa14196ca7978c506a021eef057c5cefaa544`,2882024bytes. Exact recommended features and rustc-vV are retained in build-client/.

Coin0 transfer/withdrawal PASS against retained SHA-verified37e5e133f8 control outputs: proof,public,ledger and canonical result bytes all identical. Raw records differ in seconds only. Fresh candidate generation30.434s/668612KiB RSS,exit0/swap0. Harness build57.447s/570808KiB. Initial proof-generation admission refused before execution; retry after180s succeeded. No unchanged proof run repeated.

Initial upload was refused on the55GiB aggregate reservation; first180s retry also refused; second succeeded. Every exported candidate input matches exact Git bytes(7496files). Shipped-control source identity is independently verified in control-source-identity.json. The new differential cohort is complete (details below).

## Differential completion

Fresh seeds 6000–6999: 1,000/1,000 pairs PASS against shipped `c57a344726`, using pv-integ4’s unchanged harness/comparator and three-process pipeline. This includes 600 complete proof pairs, 100 rejected-prefix pairs and four oracle-logged pairs. Canonical result records and ledger files match for all 1,000 pairs; proof/public bytes match wherever produced. Elapsed seconds alone are excluded. No discrepancy found. Full coverage, source, resource and byte-comparison receipts are under `combined/`; `stage-a-validation.json` checks the collected evidence.

Recovery after capacity error reused the still-running differential scope, without resubmission. Before recovery eight native scopes had completed and one differential scope was active; Lean/Kani attempts remain zero. No numeric native-attempt budget was specified. Refusals and cooldowns are retained; refusals started no compiler.

## First-window historical outcome (D350)

Stage A PASS: all three ELF pins, pinned client, fixed coin0 deterministic bytes, and seeds6000–6999 differential. The inherited harness covers600 complete proof pairs,100 rejected prefixes and4 oracle-log pairs across1000 paired cases; all1000 canonical records and ledger pairs match. No completed workload was repeated during recovery.

Optimized timing binary SHA256s:
- control: `1975a5d1bbdf3ca3378bd3b905f6f387862937bf019321f6f3d315c9b2cdfea6` (2570904 bytes).
- candidate: `1ee2411fadb901fa14420c9bdf719012e3012836993e7af26a3d8a1f9eb92dc7` (2972720 bytes).

Timing results (seconds; ratio of candidate/control medians):
- transfer: **INCOMPLETE**.
  all: 7 pairs; candidate median 13.971136, p10/p90 13.475419/14.587534; control median 14.010553, p10/p90 13.343688/14.288541; ratio 0.997187.
  unthrottled: 0 pairs.
  throttled: 7 pairs; candidate median 13.971136, p10/p90 13.475419/14.587534; control median 14.010553, p10/p90 13.343688/14.288541; ratio 0.997187.
- withdrawal: **INCOMPLETE**.
  all: 7 pairs; candidate median 14.073057, p10/p90 13.511129/14.309894; control median 13.884076, p10/p90 13.512598/14.617606; ratio 1.013611.
  unthrottled: 0 pairs.
  throttled: 7 pairs; candidate median 14.073057, p10/p90 13.511129/14.309894; control median 13.884076, p10/p90 13.512598/14.617606; ratio 1.013611.

Planned/completed pairs: 10/7; unthrottled 0, throttled 7; minimum unthrottled5. Measurement error: `AssertionError(('foreign capped job', 'pair-7-candidate-after'))`.
Window marker written 2026-10-28T07:34:17.558432+00:00, immutable expiry 2026-10-28T07:59:17.558432+00:00; measurement start/end 2026-10-28T07:34:27.981418+00:00/2026-10-28T07:41:30.494969+00:00; marker removed 2026-10-28T07:41:30.534168+00:00. Full package temperatures, throttle deltas and guards are in measurement/.
Native charged scopes: 14; Lean0, Kani0. Refusals consume no attempts. Every receipt records target, revision, exit, wall, peak RSS, swap, limits and axioms N/A. Task-owned Cargo target cleanup is recorded in cleanup.json; keys and raw fixture evidence retained.
Stage B INCOMPLETE: a foreign pv-b3p6-lean-42574.scope appeared during the active marker, so the guard stopped measurement. Seven completed pairs are retained; partial pair7 candidate outputs are excluded. All seven completed pairs throttled; zero unthrottled pairs, below the required five. No new window or unchanged measurement rerun was launched. Next deliverable: lead repair of cross-job quiet-window enforcement and a separately authorized timing run under a reliably quiet, thermally suitable window.

No formal premise was removed or changed. This report supplies finite functional and timing evidence for lead adoption review. Target not yet established.

Timing stopped on the guard after candidate execution in pair8 (zero-based pair7): foreign `pv-b3p6-lean-42574.scope` was populated despite our marker. Pair8 is excluded from statistics and its partial files are retained. Seven complete pairs remain, all throttled; no unthrottled gate verdict is supported. No measurement was restarted. Next concrete deliverable: lead repair/review of quiet-window admission, then a newly justified timing run with enough unthrottled pairs.
