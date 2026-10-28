# SHA453 realization and joint witness handoff

The requested local fixture obligation is established. `AspisR1.JHx_Instance.source`
proves `JHe_SHARealization` unconditionally, and `JHx_Instance.realization` installs
it. `AspisR1.JHx_Joint.source` supplies that instance to `JHw_Joint.source`.
All delivered theorems use only propext, Classical.choice, Quot.sound or subsets.
No native_decide or added axioms. No push or merge.

## Before and after

Before: `JHw_Joint.source [trees : JHe_SHARealization] (base : AdapterRw.Ops)
(stage : VTop_Stages.Ops) (slot : U64) (runtime : FixturePdaRuntime base) : ...`.

After: `JHx_Joint.source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
(slot : U64) (runtime : FixturePdaRuntime base) : ...`.

The entire existential conclusion is identical: one saved vector, original-world
TX1, corrected-world TX1, exact retained checkpoint bytes and length 1768, and TX2
acceptance on the same installed SDK. The two heaps remain explicit. Complete
statements: JHx_BEFORE.lean.txt and JHx_AFTER.lean.txt. The mechanical comparison
in JHx_STATEMENT_COMPARE.json confirms removal of only the named SHA binder;
no quantifier, dictionary, carrier, execution result or conclusion changed.
`FixturePdaRuntime base` is the sole remaining propositional hypothesis. Its
contents remain assumed; no native syscall/ELF fidelity or headline 100-bit
security claim follows from this local fixture result.

## Certificate method and checker

453 equations: tree0 Fin 157, tree1 Fin 157, tree2 Fin 139; 996 compression blocks.
JHx_generate.py independently checks each retained block's input/start/result,
all 64 SHA rounds, chaining, padding, source head/chunk definitions, input and
expected aliases, and all 453 complete digests with hashlib. `--check` validates
the exact generated source manifest. JHx_GENERATOR_CHECK.json records per-equation
digests, source pins and module hashes. Python is a preflight only; Lean checks
every concrete round. Pure arithmetic modules import JFp_SHA256 only. Equation
modules apply their compiled certificates and symbolic list/padding/hash joins.
Every delivered helper theorem has a #print axioms audit. JHx_SOURCE_AUDIT.json
records the broad-unfolding scan. JHx_FINAL_SOURCES.json pins delivered sources.

## Validation and resources

41 canonical modules have passing exact-source receipts. Budget usage:
44/60 normal attempts; 1/2 approved 16 GiB attempts.
Every attempt (including failures) is in JHx_ATTEMPTS.jsonl and its numbered
receipt directory: target/argv, source revision and hash, direct object and tool
pins, exit, wall, peakRSS, swap, cgroup limits and full axioms output. Admission
requires exit 0 AND allowed:true. One scope at a time. All swap counts 0.

Instance: JHx_043, exit 0, wall 3.971107s,
peak RSS 6624924 KiB, swap 0, source revision a3dbc5d102f38e2583eefbfe08670766d493f5e6.
Joint: JHx_045, exit 0, wall 4.899603s,
peak RSS 8266460 KiB, swap 0, source revision 39f48276abed2af98f806494941bd543a0a3fa47.
Their complete standard-axiom audits are in JHx_VALIDATION.json and stdout logs.
Total Lean wall 2616.094973s;
maximum attempt RSS 8266460 KiB.

001 failed memory after encountering padding/length/member proof errors; 003
isolated the remaining padding recursion error. Rejected sorryAx diagnostics
receive no credit. Both were replaced by changed proof shapes; neither rejected
proof shape was rerun unchanged. JHx_MEMORY_SPLIT001.md records the failures, focused
replacement and measured 16→28→56-block scale. No arithmetic cap increase.
044 failed at joint IMPORT before the post-import marker (exit 134, wall
5.289048s, RSS 7917988 KiB, swap 0). The user-approved exception authorized
045 on the same assembly in the 16 GiB scope after all three runner hashes
matched. It passed. JHx_AGGREGATION.md documents this specific exception;
only one of the two permitted 16 GiB attempts was used.
The successful probe is retained in 004's source snapshot, outside the canonical
module list. No unchanged full regression or package build was run. Final
assembly and exact-source/axiom audits consume all checked chunks. Inherited
compiled dependencies were reused, not claimed as a fresh frozen release replay.

## Cache and preservation

Own retained cache: /home/dombarker/project-offloads/codex-cx-sha453-cache-20261028.
Seeded by copying .olean companions from the read-only tx2fix and fixture caches.
JHx_SEED_COLLISIONS.json confirms no differing overlapping seed objects. Original
cache directories were never changed. Normal caps 6G/8G, swap 0, TasksMax 64, -M7000.
The approved agg16 runner hashes were verified against JHw_RUNNER_HASHES.json;
any actual agg16 use is separately receipted with 14G/16G, -M15000. Source and
receipts only are committed; no binaries, objects or oversized logs. Work is
confined to new JHx modules and evidence/joint-sha453-20261028. Existing proved
modules, Rust, protocol, wallet keys and frozen artifacts are unchanged.

No remaining blocker for this requested SHA instance and local joint witness.
The broader security target is not established by these fixture proofs.
