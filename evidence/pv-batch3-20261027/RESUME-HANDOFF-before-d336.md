# D324 handoff — checked copy packet; fresh IDs required

Exact worktree `/Users/dominic/ZK/.worktrees/pv-l3`, branch `codex/pv-batch3-20261027`. Entry/Rust freeze `0a298ad4f6d3038c9e059b06b33d3963e17013f0`; checked proof snapshot `ea0582c9b1422caf0170090a500f62660486e521`. No merge/push. Previous handoff: `RESUME-HANDOFF-before-d324.md`. Full journal: `D324.md`.

## Source and inherited gates

No repository source change under `crates/` or `programs/`. `git diff c97270adc2 HEAD -- crates/ programs/` is empty. The host mirror's three stale rejected-source files were synchronized to the lead rollback; all 523 tracked crates/programs files match, including a final recheck. Inherited c97270adc2 receipts apply: all three ELF pins, both native variants/all 11 terminal point shapes, worst measured per-call cost projection +1.906124819123782%. No ELF/cost/full-fixture rerun.

Pins: default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`; devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`; Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.

Both rejected counterexample binaries remain on the host under `bin/`, hashes `fe278db2829e72ecbbbc61702042427c6152d9f9341702965c8aa457bfad54a3` and `f7e59b38d874885a680737e4e84e16c1bc2d5a7235e0b502dda57f9f2fe6884b`. No keys/nonce ledgers deleted. No own scope remains. Private caches are retained for the pending continuation.

## Budget and admission

79/85 new charged Lean attempts: 65 accepted, 14 rejected; Kani 0. Historical tally was 15 charged attempts. All assigned IDs 37916–37999 are now consumed. Five admission-only refusals (37981, 37983, 37990, 37993, 37995) charged zero; their retry gaps were 197.0–201.7 seconds. Historical 37907 also consumed an ID without charging an attempt. Thus six charged attempts remain authorized but require fresh unused IDs. Requests were sent; no new range was allocated independently. `TALLY-d324.json` retains the old focused pointer 37997; **it is used**, as are 37998/37999. Do not retry any assigned ID.

The queued standalone PolynomialEmission compile was blocked by the focused-ID guard before launch/ID consumption. Its eight exact declarations were then checked with the source audit. No fixture disagreement, ELF mismatch, cost violation or checked ROWS5 counterexample occurred. Failed proof drafts were retained and did not stop the work.

## What passed

- **222:** optimized same-input native/emission comparison passes: all-zero point, constant-seven length-1024 column, native original=copy=emission `[7,0,0,0]`. Native receipt exit 0, 38.262 s, 569888 KiB RSS, swap 0. `PV_B3_MultilinearFinite222.source` proves arbitrary-input complete-Result copy factorization. `PV_B3_EvalFold222.source` connects evaluation to list fold under its explicit `i≤len≤1024` metadata bounds. Prefix, suffix, inner-weight, outer-storage and evaluation loops have named decreasing-rank proofs. Original sparse-iterator/list construction equality and universal native original/copy equality remain open.
- **134:** seven R1Z sources resolved under h5 and compiled privately. `PV_B3_MaskDictionary134.copy_reference`, `.dictionary`, `.op134`, `.nonvacuity` pass: complete-Result translated copy/reference equality, whole dictionary equality to the established reference selection, exact 64 masks and a successful witness. `PV_B3_AuditSourceD324.Errors134` proves lossless error/Result roundtrips and no hidden success. Native original/copy association is inherited measured evidence; native/adoption integration and the row closure are not claimed.
- **117:** `PV_B3_Range117` proves arbitrary-raw-input equality of the copy's 16/10 scatter and 26 descending prepared-Horner expansions with list traversal. Generator `--check` and frozen-Rust token-shape checks pass. `PV_B3_AuditSourceD324.Mask117.source` composes the complete root-to-traversal equation. Original field/helper correspondence remains open.
- **121:** `PV_B3_AuditSourceD324.Poly121.source_complete` proves the full-Result bounded reference for the exact grouped block evaluator on arbitrary raw coefficients/challenge. Eight raw declarations are included byte-for-byte from PolynomialEmission; linkage SHA is recorded. No naive-Horner replacement or canonical-input assumption was introduced. Universal native original/copy equality and row/model interpretation remain open.

Ruling (n): 222's updated array is threaded forward; its identical-input native check is new. Existing 134/117/121 restoration scans/native comparisons are reused; the exact inline121 section preserves every continuation application. These runtime checks do not supply the missing universal source laws.

## Final audit and receipts

37998 `PV_B3_AuditSourceD324`: exit 0, 3.382 s, 2698764 KiB RSS, swap 0. 37999 `PV_B3_ClosureD324`: one combined audit of 912 prerequisite theorems followed by the focused closure theorem in the same target; exit 0, 4.073 s, 2673840 KiB RSS, swap 0. All 913 final reports are subsets of `{propext, Classical.choice, Quot.sound}`. The complete closure statement is printed in its log; it asserts copy/control/carrier facts, not native source laws or privacy closure.

Before first compile and again before the final target, all 5673 external objects match h4 manifest SHA `d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e`. Actual env-J external selection also matched. No shared sources/objects written; no external object rebuilt/substituted. Seven project R1Z sources use own-HEAD h5 pins. Original-body reference import scanning retains unresolved `ProverRwSampler.Funs` variants; neither was imported, and no cohort inconsistency is asserted. Further freeze-record resolution is needed before that route is compiled.

`d324-receipt-index.json` contains every new charged receipt and complete wrapped axiom report. Raw snapshots/logs are in `receipts/lean-37916` through `lean-37999`. `d324-accepted-source-bindings.json` SHA-binds all 65 credited sources to git. The raw37998 proof-head label predates its correction; its source snapshot/hash is exact and the index supplies a matching handoff revision. Maximum Lean RSS 2837400 KiB, all swaps zero. Caps stayed 6G/8G/swap0/Tasks64, Lean -M7000. `d324-object-inventory.json` records the retained private objects.

## Residuals and next work

Rows closed **0**; no premise removed, added or weakened. All original statements/quantifiers and ExternalFuns residuals remain P/OPEN in `d324-row-status.json`, including V217, V220, V230, V239 and the other six rows. T is exactly entropy_law, entropy_kernel, observation. D234/V403, deployment/E1/E2, real RunJoin, client proof-account route and L1/L2/L3 remain open. **Target not yet established.**

Next: allocate fresh IDs for the remaining six charged attempts; retain/reuse this private cache. First prove the original sparse iterator's constructed list equals222's populated array prefix and discharge the reached metadata bounds, then compose its native/source row bridge. Complete134 native/adoption association and117/121 original-helper transports/row bridges in the requested order. No Rust change is authorized; stop/report if one appears necessary.
