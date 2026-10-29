# N73509 combined-client paired timing

PASS under owner-adopted D359(A), evidence class **measured under throttling, paired**. Only N73509 ran; N73512–N73514 remain unused (N73510–N73511 were historical bundle audits). No build, ELF, differential, CT, Lean or Kani gate was repeated. No merge, push, deployment or shipping repin.

Frozen gate packet: `683e01efeef0f86ad66359163550c0325a8fabba`, branch `codex/pv-c474-draft-20261029`, worktree exactly `/Users/dominic/ZK/.worktrees/pv-c474`. Production inputs and the earlier packet are unchanged; this continuation adds timing scripts and receipts only.

| Fixture | Shipped median | Combined median | Candidate/shipped | Change | Gate |
|---|---:|---:|---:|---:|---|
| Transfer | 14.3587051765 s | 14.8349470545 s | 1.0331674669 | +3.3167% | PASS |
| Withdrawal | 14.5008873880 s | 14.3100642805 s | 0.9868405910 | −1.3159% | PASS |

Ten alternating paired samples per fixture (40 actual-client executions total). Every rolling median ratio was at most 1.10; both final candidate medians were below 15 s. These are the frozen stdout `prove_wall_seconds` gates; independently recorded process-wall medians were 14.846505 s candidate / 14.370700 s shipped for transfer and 14.321698 s / 14.512280 s for withdrawal. All ten pair groups were thermally throttled; no unthrottled samples exist. Ninety before/after inventories found no foreign populated finite-memory user cgroup. Samples are finite timing evidence; they do not establish a universal unthrottled bound or whole-client constant time.

Candidate SHA-256 `da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0` (2,281,512 bytes). CURRENT shipped control from the frozen packet: `30d883a8d97f12c315898aaf9170eb7a542b5e935881f089506fd4601ddb6a20`. Both verified before execution, in the harness, and after execution. Neither was rebuilt. `timing/binary-pins.json` and `post-run-binding.json` record the exact host paths.

Ruling (e′), D533: marker `until=1793263180.3563738`; first timing guard current time `1793306354.777771` (`2026-10-29T20:39:14.777771Z`). The marker was expired and not in force. Its unchanged SHA-256 is `7247d32316b1c4bfb61f0fc907ec521b5170738a2526df4998c6cb52159a2b0b`. No marker was edited/deleted or new window claimed; normal reservation admission was used without QUIET_WINDOW_OWNER. Each of 90 guards records marker and current time. `timing-adaptation.diff` changes only output destination, candidate hash binding and the stale active-owner guard; pairing, thermal checks, foreign-job checks, samples and thresholds remain unchanged.

N73509: exit 0; wall 9:38.95; maximum process RSS 600,052 KiB; swaps 0; MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Exact target, source revision, admission/barrier decisions and `/usr/bin/time -v` output: `native73509/`. `#print axioms`: N/A, native timing only. Time was spent generating proofs with existing optimized clients, not compilation. Keys, proof outputs and ledgers remain on the assigned host; no transaction was broadcast or key cleanup performed.

`verification.json` independently recomputes all rolling gates and checks all inventories, marker observations and post-run hashes. Initial local receipt verification expected 50 inventories; corrected to the actual 90 (10 pair-start + 80 call-boundary checks), with no native rerun.

This closes only the combined-client timing gate previously blocked before launch in `evidence/pv-c474b-20261029/BUNDLE.md`; its expired-marker blocker is superseded by D533 and these results. Other gate results are reused unchanged. No endpoint premise or T field is removed, added or weakened. V370/V371, E1/E2, whole-client side channels, source/native observation binding, RunJoin and shipping adoption remain; privacy target not yet established. Next deliverable: lead reviews/adopts the completed gate packet and pv-cx consumes the already-pinned extraction spans.
