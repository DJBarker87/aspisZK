# D561 report — READY-TIMING preparation; formal gate FAIL

Branch `codex/pv-uc-20261029`, continuation base `a24c4f7e6d`; production source finalized at `3161f53b0c`. This report supersedes [D543](REPORT-D543.md). **The full entry compiles parametrically, but fails the standard-axioms audit. PrivacyR1HeadlineDeployedReal.privacy_headline_deployed is not established; no premise was removed.** Timing preparation is ready for the lead; no new timing run was launched.

## Gates and evidence

| Gate | Result and evidence |
|---|---|
| Historical large differential | **PASS N75145, 1,000/1,000 pairs, 2,000 real prover calls**, retained without replay; historical report and receipt |
| Final client differential | **PASS N90114, 100/100 pairs, 200 real prover calls**; [public metadata](final-gates/ready/differential-public.json), [receipt](native90114/receipt.json) |
| Final optimized build | **PASS N90113**; [recipe, sources and hashes](final-gates/ready/build.json) |
| Three release ELF identities | **PASS N90113** retained bytes match all three pins; N75137/38/39 fresh build evidence reused |
| Fixture target | **UNCHANGED** source and executable hashes, N90113 |
| Decoder Funs | **PASS Lean75006** after actual Rust shift-type repair; unchanged Types reused |
| Decoder execution | **PASS finite 3/3 complete 263-value vectors** (zero/ff/ramp 212-byte records), Lean75038, [comparison](final-gates/d561/decoder-execution.json); not a universal theorem |
| Final entry Types/Funs | **COMPILE PASS Lean75028–75033**, explicit 22 carrier/104 operation parameters; native instances remain obligations |
| Formatting congruence | **PASS Lean75036**, six local theorems, standard axioms only; public-argument/native-binding hypotheses remain explicit |
| Raw audit | **FAIL for main**, **42 unapproved native-decision axioms**, Lean75039; seven component roots standard-only; [validated walk](final-gates/d561/axioms/validation.json), [failure inventory](FORMAL-FAILURE-D561.json) |
| Last literal-bound repair | **FAIL Lean75040**, no object/credit; primitive literal UTF8 size does not kernel-reduce |
| Timing preparation | **PASS 17 offline guard tests**, [log](timing-window-offline-tests.txt); read-only persistent bus API probe passed, zero scopes/prover calls/samples |
| Timing measurement | **NOT RUN in D561**, explicitly deferred to lead. Prior N75143/N75149 samples remain INVALID; no accepted timing verdict |
| Decoder instruction trace | Historical finite N75140 evidence reused for unchanged decoder shape; no new whole-client trace or CT claim |
| Full frozen manifest/release replay | **NOT RUN**, standard-axioms/native-binding prerequisites failed; no unchanged large regression |

N90114 exit0, wall33:31.76, GNU-time peak604,220 KiB per process; aggregate cgroup peak1,798,848,512 bytes, swap0, OOM/task-limit events0. Actual work was optimized proof generation, semaphore3, 50 transfer and 50 withdrawal pairs. All receipts record command, source revision, wall, RSS, swap and axioms status. Aggregate cgroup resources supplement GNU time. Private inputs/proofs, wallet records, nonce ledgers and keys stay retained on the host; only comparison metadata/digests were collected.

## Client source repair and regression scope

[Patch](PATCH-D561.diff) changes only five files in `tools/r1-cost-probe/src/bin/user_client*`. Actual Rust shift literals now use U32 (`32`, `20`, `1`, `4`), preserving values, bits and panic/overflow conditions. Typed helper boundaries retain operands for pure JSON constructors, consuming array projection, public lanes/capacity, public-key/String parsing/rendering and wallet I/O. Renamed locals avoid Lean keywords/shadowing. Protocol/prover/crates/programs, manifests, locks and the fixture target are unchanged. [Scope assessment](RESUME-D561.md) records each repair; [build source binding](final-gates/ready/build.json) checks mechanical normalization to original hashes.

Rendering stdout JSON now creates an infallible formatting String and emits raw bytes plus newline. Successful compact JSON bytes and keys are preserved. Allocation/drop timing and write grouping changed and remain native side-channel/failure obligations; trace identity is not claimed. Panic diagnostics and recovery writes remain. No key material was deleted, refunded, transferred or accessed for cleanup.

The requested **100-pair subset** covers both fixture actions and final client wiring with the unchanged comparator, fresh nonce labels and complete actual prover execution. It checks statement bytes, all compiled proof-input fields and JSON/instruction outputs (only the pre-registered elapsed-time field and removed fixture mask key are excluded). Random proof bytes are not compared. The affected code is client decoding, formatting and extraction boundaries, while cryptographic bodies, feature set, fixture/protocol encodings and release ELFs are unchanged. Thus the 1,000-pair gate and unrelated runtime/adversarial/reproducibility suites were reused. The subset is finite regression evidence, not universal equivalence or timing evidence. N90102's earlier40 pairs are SUPERSEDED, not added to100; its authoritative signal exit143 is preserved in reconciliation.

Final user_client SHA256 `2ff137efbd45933fa0d4e4564526637547492c6b1eefc682039959887a5450a6` (2,028,384 bytes). Fixture SHA256 `6db76577e5f3331152bbcd6c22739ceea1e0413ed77cf34f10789f4d72488194` remains unchanged. Rust1.94.1, optimized client profile(opt3, panic abort), locked/offline, `r1p-check,aspis-r1-cost-probe/ct-host-prover`; exact commands/environment/audit hashes in build.json. Retained ELF pins: default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`, devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`, pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.

## Public arguments and findings under revised fmt-1(b)

The simulator needs a deterministic pure String function on public arguments, not a faithful TEXT model. [Source/data-flow inventory](formatting-flow-d561.json) anchors each formatting/serialization call and output field. FD-path formatting takes only public `q.wallet_bytes_fd`, before private read; local congruence for the actual extracted call is proved. String writer success does not imply allocator/OS failure independence. Actual stdout I/O remains separate and fallible.

**FMT-ELAPSED-ARG:** `Number::from_f64(started.elapsed().as_secs_f64())` spans witness handling, selection and proving; it is not derived from public request. Honest-run witness independence remains unproved.

**FMT-TRANSCRIPT-ARGS:** `render_json(out)`, selected pubkey rendering, retry/proof-length number conversions, instruction hex, statement/proof serialization consume protocol outputs. Public/simulated status requires the existing E1/E2, retry and transcript laws. Printed output is not automatically public. The six congruence lemmas explicitly assume public argument equality and shared pure formatter bindings, allowing distinct effect records/private inputs.

**FILE-RECOVERY-SECRET:** `wallet::retain -> write_all(record)` directly serializes all 212 secret wallet bytes. It is neither public nor witness-independent. The retained file is mode0600 in a mode0700 directory. Whether that private sink is excluded from observer-visible bytes is an unproved boundary; deleting it would hide the finding and violate retention rules.

Private input remains exactly212 bytes: input key/salt/value/asset; change key/salt; recipient key/salt/value. Action, amount/destination, chain/account keys, lane/checkpoint/complete eight-lane leaf sets, proof-account candidates and output directory are public JSON. [DESIGN](DESIGN.md) and historical report contain offsets. Membership selection, rejection, allocation, I/O and timing remain whole-client obligations.

## Formal result and stop reason

Pinned Charon `daad69be…` and accepted ae1-2 Aeneas `fda587d2…` regenerated the actual client. Computational bodies were not hand-edited: `entry-parameters-ready.py` inverse-checks namespace/import/binder changes only. F64 is an explicit U64 bit carrier at an opaque boundary, with no native arithmetic law claimed. The native P constant uses the actual field literal. No external axiom template was installed as a global implementation, and no result relies on builtin Unit formatting.

Every compile checked all 5,673 external objects against h4 authority `d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e`. No library object was rebuilt/substituted. Lean75039 walks declaration types/values, reconstructs import DAGs, checks serialized/kernel inventories, and agrees with collectAxioms and #print axioms. main reaches 5,234 constants and 42 compiler-created `_native.decide` axioms from Aeneas toStr default UTF8-size proofs. They are rejected, despite entry compilation. Seven roots (decoder +six formatter lemmas) pass standard-only. Earlier75026's Formatter-axiom result is not credited. Lean75040's proof-only bound replacement failed; it is retained solely as failure evidence.

**40/40 Lean attempts used, zero remain** (75016 was an unlaunched refusal, uncharged). No further Lean probe was run. New native allocation:15/20 used, five unused N90115–N90119. N90108 macro-import build failure and N90102 superseded termination remain recorded. No capped job remains active. All jobs used 6G high/8G max/swap0/Tasks64, Lean-M7000, one own scope at a time. No full manifest was attempted after the failed focused prerequisite.

Before/after endpoint statements and deployment premises are unchanged: rows removed=[], added=[], weakened=[]. T remains exactly entropy_law, entropy_kernel, observation. Native bindings, actual RunJoin, E1/E2, V370/V371, L1/L2/L3, failure-event independence and private-storage boundaries remain P obligations; no obligation was folded into T. Next formal deliverable with new budget: symbolic UTF8/ASCII literal bounds or typed public selectors removing toStr literals, then smallest changed file and audit. Not a privacy/release-ready result.

## Lead-only timing command

The window-aware runner requires a LIVE marker with `for = pv-uc-timing`, refuses foreign/malformed/expired/absent markers for timing, checks normal admission exit0 AND allowed:true, native901xx ID and exact caps. It records load/thermal counters, uses fresh per-scope output/nonces, monitors every 50 ms and subscribes persistently to this build user's systemd UnitNew events. A foreign capped scope, even a queued transient same-user scope, invalidates the pair and terminates/reaps the client; unavailable observation fails closed. Other-user finite cgroups are inventoried; no universal arbitrary-other-UID subinterval claim is made. The shared marker/tools were not edited. The real bus probe created no scope and measured no prover.

**READY-TIMING; do not run until the lead arranges the named window with Stream A:**

```sh
python3 /Users/dominic/ZK/.worktrees/pv-uc/tools/pv-uc-20261029/scope901.py native90115 d561-timing python3 /home/dombarker/project-offloads/codex-pv-uc-20261029/timing-window.py
```

The next ID is unused; five authorized native scopes remain. This readiness is preparation only. No timing verdict is claimed. [Commit list](COMMITS-D561.txt) and per-ID receipts supply revision history; nothing was pushed/merged/repinned.
