# D543 final report — minimal user client gates incomplete

Branch `codex/pv-uc-20261029`, exact worktree `/Users/dominic/ZK/.worktrees/pv-uc`, base `683e01efee`. **Privacy target not yet established. Rows removed: NONE.** This proposed bundle is not adopted, merged, pushed or repinned. [COMMITS.txt](COMMITS.txt) records `git log --oneline 683e01efee..HEAD` through the report's preceding commit; the final report commit follows that snapshot.

The existing N75145 run was waited for and recovered **without resubmission**. Its full result is **1,000/1,000 passing pairs**, 500 transfer and 500 withdrawal, with 2,000 real optimized prover calls and no mismatch. The full-entry Lean gate remains blocked, and the one admitted D359(A) rerun was invalidated by foreign activity after quiet admission. [gate-status.json](gate-status.json) is the machine-readable gate summary.

## Every gate

| Gate | Final result and evidence |
|---|---|
| Three release ELFs | **PASS** N75137/38/39 against the frozen SHA pins. Original rebuild receipts and `final-gates/elf-{default,devnet,pool}/comparison.json` retained. N75150 checks their hashes again; no successful build is replayed. |
| Final user executable and recipe | **PASS** N75136. SHA `9310ca5e3dcb3b2e8d7ac51312d6737aa465d2f8321fdaef6928114ffa38538e`, 2,029,480 bytes; exact recipe in [final-build.json](final-build.json). N75150 confirms unchanged bytes. |
| Separate fixture/SDK target | **PASS** final build; unchanged fixture source against base. Harness SHA `6db76577e5f3331152bbcd6c22739ceea1e0413ed77cf34f10789f4d72488194`, unchanged from N75121. Its current SDK dependency pin is preserved. No identity with the historical bundle's different binary is claimed. |
| 1,000-pair differential | **PASS N75145**, exit 0, 1,000/1,000, 2,000 actual prover calls. [summary](final-gates/differential/summary.json), [all comparisons](final-gates/differential/comparisons.json), [receipt](native75145/receipt.json). Statement bytes, every serialized compiled proof-input field, output and instruction bytes match. Only pre-registered removed `mask_audit` and separately measured timing are excluded. No random proof-byte equality claim. |
| D359(A) user versus preregistered shipped baseline | **INVALID / INCOMPLETE N75149**. Quiet pre-admission load 0.605 / 1.553 / 5.547, no other capped user jobs. A foreign capped Lean scope appeared during the first transfer pair; the post-call guard rejected it. **Zero accepted complete pairs**, no median/ratio verdict. [verdict](final-gates/timing-d543/verdict.json), all before/after quiet/load records, marker records and [receipt](native75149/receipt.json) retained. The one admitted rerun is used; no repeat. |
| Labelled constant-time decoder check | **PASS N75140**, instruction-trace comparison: zero/ff/ramp records follow the identical 63 instructions including libc memcpy, with every decoded field and retained byte checked. [ct-decoding.json](final-gates/decoder/ct-decoding.json). Finite decoder slice only; not dudect or universal latency/whole-client constant time. |
| Charon/Aeneas full-entry emission | **PASS N75135 emission only**. [extraction75135](extraction75135/) contains unedited output. N75150 confirms all four original output/template hashes. |
| Full-entry Types/Funs compilation and faithful external binding | **BLOCKED / NOT PASSED**. `lean75002` stops at missing `PVUCEntry.TypesExternal.olean`; 25 type + 119 operation declarations remain uninstalled templates, not axioms installed in a credited environment. Observable formatting loses required operands before its external boundary. See [EXTRACTION-BLOCKERS.md](EXTRACTION-BLOCKERS.md) and [external-boundaries.json](external-boundaries.json). |
| Focused decoder Lean / D188 executable comparison | Types **PASS 75000**. Verbatim Funs **FAIL 75001**: `U64.wrapping_shl i5 32#i32` supplies I32 where the authoritative library expects U32. No emitted-body/library repair or unchanged failed resubmission. Prepared emitted execution is **NOT RUN** because its Funs prerequisite failed. Syntax inspection alone earns no D188 credit. |
| Axioms audit | **PASS only for the two formatting diagnostic theorems and Wallet type**, 75005. Raw kernel-body walks equal collectAxioms and printed axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [validation](final-gates/axioms/validation.json), reachable inventories and [receipt](lean75005/receipt.json). Full entry and decoder Funs are unavailable and **not audited**. |
| Final source/artifact binding | **PASS N75150**, 31/31 hashes: production source/manifest/lock inputs, client/fixture/audit executables, release ELFs, original full-entry emission/templates. [final-audit.json](final-gates/final-audit.json), [receipt](native75150/receipt.json). This is checksum binding, not all-gates success. |
| Final dependency-closure replay | **NOT RUN**, because focused Funs/full-entry/binding prerequisites fail. No unchanged full regression or cold dependency rebuild was started. |

## Differential and resource receipts

N75145 source revision is `bbb8ac9a884b086a8dc5a8cf02e12180abf985a1`; its source-input hashes and audit-build pins bind the actual run, rather than attributing it to a later evidence-only HEAD. Wall **5:32:32**, max process RSS **608,728 KiB**, cgroup peak **2,234,355,712 bytes**, swap **0**, no OOM or task-limit event, final scope inactive. The differing RSS/cgroup measurements are both retained. All proof inputs, proofs, wallet recovery records and nonce ledgers remain on the host; only comparison metadata was collected. No corpus duplicate or replacement run exists.

The audit copies preserve the entire prover call, with one additive binary input capture immediately before the unchanged `RealR1_client::prove_for_proof_accounts` call. The capture uses explicit field serialization, not Debug. [audit-build-fixed.json](final-gates/audit-build-fixed.json) pins their sources and executables. Any byte difference would fail the unchanged comparator; none occurred.

## Private/public input boundary

| Input | Visibility | Encoding/location |
|---|---|---|
| Input note nullifier key, salt | Private | 32 + 32 bytes, offsets 0–63 |
| Input value, asset | Private | u64 LE + u32 LE, offsets 64–75 |
| Change nullifier key, salt | Private | 32 + 32 bytes, offsets 76–139 |
| Recipient owner key, salt, value | Private | 32 + 32 + u64 LE, offsets 140–211 |
| Wallet record | Private | Exactly 212 bytes on inherited raw FD plus EOF; recovery retained with restrictive permissions |
| Action, amount/destination, transaction/account keys | Public | JSON |
| Lane bytes, checkpoint, complete eight-lane pair-leaf sets | Public | JSON, independently supplied from the selected secret note |
| Proof-account candidates, output directory | Public | JSON |

[DESIGN.md](DESIGN.md) was committed before Rust changes. Membership is computed locally after non-selective public lane input; per-leaf network acquisition is prohibited. Whole-client membership selection, rejection, allocation, I/O and timing remain observable obligations. Fixed decoder offsets do not make those operations constant-time. `mask_audit` was removed because witness independence was not established; fixture fields are absent only from the user target. The separate fixture target is unchanged. No proof/public-statement or TX1/TX2 layout change is adopted.

## Checked model obstruction, not a privacy closure

`lean75003` proves `PV_UC_FormattingObstruction.fdArguments_equal` and `no_faithful_fd_formatter`: the current builtin formatting arguments erase their operand, so an external pure formatter cannot reconstruct both `/proc/self/fd/3` and `/proc/self/fd/4`. N75147 validates the exact reached expression under optimized Rust 1.94.1 and obtains those distinct strings. This is a **negative model diagnostic**, not a source law or a D525 wire mismatch. Native/source/library/emission pins and scope limits are retained in [formatting-obstruction](formatting-obstruction/). No rejecting-writer instance, arbitrary external definition, new axiom, or formatting-unreachability assumption is introduced.

The JSON printing path also reaches the erasing builtin. `(fmt-1)` still requires faithful observable writer/error-state semantics or approved source removal. The 144 remaining external declarations include native I/O, JSON, hashing and the prover boundary. Compilation cannot legitimately be manufactured by installing their axiom templates. The two checked blockers are documented in [EXTRACTION-BLOCKERS.md](EXTRACTION-BLOCKERS.md); those steps are stopped, not silently weakened.

Accepted translator SHA `fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68` is the pv-cx2 **functionally identical rebuild (ae1-2)**; Charon SHA `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`. Their identity/regeneration evidence is reused, not a new tool-trust item. Every Lean compile verifies the h4 authority SHA `d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e` and all 5,673 external objects with first-root resolution; [authority check](lean-object-authority-check.json). Private objects are built/reused only in this job's pinned workspace. No library object is rebuilt or substituted, no soundness cohort is imported, and no duplicate-origin/feature equivalence is assumed. Reached nightly-versus-1.94.1 std/source associations remain obligations under (x') and V370.

The raw audit visits declaration types and values, checks serialized/kernel axiom inventories, reconstructs import DAGs and validates reachable sets. Its roots visit 2,045 / 2,106 / 1,996 constants respectively. Each root closure contains 3,938 modules; 24 loaded axioms are inventoried, including imported nonstandard axioms shown unreachable from these roots. This cached-authority focused audit is not a cold coherent release replay.

## Timing refusal, invalid samples and accounting

N75148 was refused **before admission**, when `pv-b3p6-lean-79728.scope` appeared after an earlier quiet probe. No scope or timing sample ran; the ID is retired. A full 180-second cooldown preceded the next ID. N75149 then admitted in a newly quiet environment and executed the single authorized rerun. A foreign capped Lean scope `run-r8cdd4a24c6c447139f14433d5ebdc3e2.scope` appeared during it. The retained, **unaccepted** transfer call durations are baseline 12.909407617 s and candidate 13.285308944 s; they are not medians, an accepted paired result or a performance pass. N75143's earlier invalid run is also retained. The combined-client timing was never repeated. Expired shared marker contents were read and preserved, never edited or bypassed.

N75146 stopped before compilation because the own diagnostic's PATH omitted rustc; N75147 records a changed absolute tool path and reuses the same retained partial directory. No unchanged failure is hidden by a fresh destination. All scopes retain 6G high / 8G max / swap 0 / TasksMax64, Lean -M7000; every launched receipt includes exact target, exit, wall, peak RSS, swap, source revision and axioms status. The optimized prover remained the heavy step in N75145; caps were never raised. [attempts.json](attempts.json) indexes all receipts and refusals.

Final use: **50/50 native scopes**, **6/40 Lean attempts** (4 success, 2 failures), **0 Kani**, no pending own work. N75148 is an uncharged retired refusal. Next IDs would be N75151 (no native budget) and 75006 (34 Lean attempts remain). The formal items stop on the checked required-emission typing failure and model information-loss obstruction. Additional arbitrary Lean attempts cannot supply the missing faithful interfaces; no unchanged failure or successful frozen regression is replayed.

## Retained premises and next deliverable

Before/after, no hypothesis of `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` is removed, added, weakened or changed. T remains exactly `entropy_law`, `entropy_kernel`, `observation`. E1/E2, V370/V371, real RunJoin, native I/O/JSON/hash/formatting association, entropy/OS-failure adequacy and whole-client L1/L2/L3 remain open. Neither native fixture equality nor the negative formatting theorem establishes privacy.

Next concrete deliverable: source-faithful handling of the shift operand and formatting operands under the unchanged accepted extractor, faithful external bindings, then full-entry Types/Funs compilation and an audit/replay of that actual closure. Any source/artifact change needs a covered-gate reassessment. Valid D359(A) evidence still needs a protected quiet period and new authorization/budget, because the one admitted rerun here is used and the native ceiling is exhausted.

All task keys, recovery records, nonce ledgers, fixture SBF keypairs and required caches remain retained. The deployment authority directory was not read or touched. No RPC, network gate, devnet access, broadcast, cleanup, merge, push or repin occurred; SSH was build-host transport only. **Privacy target not yet established.**
