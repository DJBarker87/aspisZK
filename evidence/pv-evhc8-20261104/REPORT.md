The single authorized agg16 attempt 92060 FAILED at step 3. The composition does not count.

Worktree: `/Users/dominic/ZK/.worktrees/pv-evhc`; branch `codex/pv-evhc-20261029`; revision `b1c3f49bf70cdb2022e5d98f61a93c36576ebeb8`. No commit or source correction was made after the failed attempt.

Admission passed once: `allowed:true`, reservation exit 0. Lead runner SHA-256s matched `d6d40da5`, `9b325ab0`, `8165ccff`; full hashes are in PREFLIGHT.json. All 33,251 pre-existing combined objects/companions were hash-checked before admission and rechecked inside the scope before compilation. All 16,058 NER modules, every NER cohort companion, the five explicit NER_REBUILT_OBJECT_PINS.json entries, and the fresh 594-module overlay matched. Authority files were obtained from research and matched the prior pinned authority. The original temporary runner prompt was missing; its archived repository copy supplied the procedure.

| Step / exact target | Exit | Wall (s) | Peak RSS (KiB) | Swap |
|---|---:|---:|---:|---:|
| 1: PV_BR_FixtureConsumer | 0 | 6.908572 | 8718176 | 0 |
| 2: NER_SCAN full combined import closure | 0 | 75.188970 | 12322680 | 0 |
| 3: NEP raw walk: all consumer roots and both soundness roots | 1 | 0.683067 | 1567052 | 0 |

Scope `pv-evhc8-92060.scope`: exit 1, wall 95.496436 s, peak RSS 12322680 KiB, swaps 0; cgroup peak 6169735168 bytes. Enforced MemoryHigh 14G, MemoryMax 16G, MemorySwapMax 0, TasksMax 64; every Lean command used `-M15000`. The runner receipt records the exact commands, revision, limits, source hashes, and all available `#print axioms` output.

Step 1 PASS: PV_BR_FixtureConsumer compiled from unchanged source SHA-256 `48381d7a82300eadec1f5973cd87bd5b4119d1f399717d9210263e379ef1297e`. Consumer object hashes are retained in CONSUMER-OBJECT-PINS.json. Full compiler output and axiom summaries are in step-1.log and step-1.json. These summaries are not raw-walk evidence.

Step 2 PASS: full combined import closure, including the consumer and both soundness branches: 16,539 modules, 1,593,937 declarations, 39,863,671 reference edges, ZERO dangling references, every import list matched. The scanner namespace is byte-identical to NER_FinalDriverV2.lean; importAll=true, private level, loadExts=false. Full per-module results are preserved in COMBINED-SCAN-ROWS.jsonl (SHA-256 `909aba6993d91998e3218fc5cd2842b0111f2aada1b1258697da68159e5e3c55`), with SCAN.json and the exact manifest/expected module set.

Step 3 FAIL: NEP_Driver.lean:4:42 could not resolve CommandElabM. I embedded the unchanged NEP walker body before its required `open Lean Elab Command` declaration. The adapted driver failed elaboration before any audit ran; the subsequent `sorry` warning is compiler recovery from this error, not a successful audit. Full output is retained in step-3.log. No consumer raw-walk axioms were produced, and neither the 115,256-constant deployed-root check nor the 885,736-constant sourceOnHeadline check ran. RAW-AXIOMS.json explicitly records both as NOT_RUN. Matching standard axioms for the soundness roots are therefore NOT established in the combined environment.

Stopped on the first failed step, with no retry, cap change, alternate launch, or post-failure Lean execution. The failed driver is preserved exactly as launched. The fixture witness retains FixturePdaRuntime base and does not prove event acquisition or joint simulation links.
