# S6 native transport handoff

Branch `codex/cx-s6-native-20261026`; commits local, no push. **Assigned deployment row L176 removed on `AspisR1.S6N_Top.deployed` under the binding D188 safe Vec/Box ruling. Global S2 and the release target remain open.**

## Established and retained

The actual semantic_public/common getters and public decoder Box layers are safe Rust; they take arm(a) of the ruling, not the unsafe/reference arm used for NP6's uninit construction. The current decoder source and all relevant field/format helpers match the frozen extraction source (unrelated proof-only tails excluded explicitly). Safe ownership/Box/error cleanup uses the existing Aeneas standard model and Allocator item; no trust is added or widened.

`lean/S6N_Decoder.lean` proves complete Result/error/context transport. `S6N_Getters.lean` proves both actual field projections and their exact semantic carrier. `S6N_Installation.lean` derives the concrete installed SDK facts, without a native equality, decoder-success or cleanup premise. `S6N_Top.deployed` retains the exact Rc7 antecedents and all original conclusions, adding those derived facts on the SAME selected dictionary. Native K004/K005 check actual typed field-pointer identity, real Box/drop, leak/cleanup and reachable returns for arbitrary full native carriers. The safe decoder itself is NOT claimed universally re-proved by Kani: its authorized route is safe extraction/D188.

Before/after: S6N_BEFORE.lean.txt / S6N_AFTER.lean.txt. Mechanical recount: S6N_RECOUNT.json and S6N_LEDGER_DELTA.md. Actual antecedents stay83T/26P/13G; deployment-only P5→4; deduplicated89T/31P/13G→89T/30P/13G. This is one deployment-row removal, not a claim of fewer logical binders. Shared ledger/session A files are untouched; lead integration should adopt this prefix-only top and delta.

Non-vacuity: additional Facts holds unconditionally for every configuration, so the antecedent domain is unchanged. Optimized R001/R002 successfully encode/decode BOTH real1880-byte variants with exact content, getter identity, drop and WrongMagic rejection. Getter covers pass. Existing Rc7 conditional composed non-vacuity is preserved. No deployed accepted cryptographic spend fixture is claimed.

## Validation and budget stop

**100/100 Lean attempts used:99 passes, one excluded elaboration failure; zero dependency builds. 5/40 Kani invocations:2 semantic passes,2 setup failures,1 excluded large-memcmp unwind failure. 2 optimized native fixture attempts pass.** Prover work stopped at the Lean limit. The95 fresh kernel inventory targets cover168 reachable decoder definitions plus the final new-theorem/top audit; these are source/trust evidence, not extra security theorems. No package replay ran.

Top L005: exit0, wall3.441067464009393s, peakRSS5502124KiB, swap0, revision9566554995240c7ff8e721680faf28cf86abdf68 plus exact dirty snapshot. Final L100: exit0, wall3.7345425519743003s, RSS5476068KiB, swap0. All ten new theorem audits use only propext/Classical.choice/Quot.sound. Total Lean command wall317.14691947045503s. Every job has verified6G/8G/Swap0/64-task scope, exact command/source/dependency pins and full axiom/error output. Nine transient reservation races each received the required30-second single retry; no bypass, cap increase, OOM, timeout or unchanged retry.

S6N_check.py passes all107 receipts, source pins, frozen identity, exact antecedent comparison, inventory coverage and native covers/fixtures. Raw whitespace-only log normalization is exactly reversible and hash-checked. No shipped/cfg(kani) file changed, so no ELF rebuild trigger. Inherited defaultf8c0ec72…, devnet63ad3e9c…, Pool121f3e29… pins were not freshly reproduced. No binary/object/archive/key is committed or destroyed.

Retained: existing SDK/allocator/runtime/extraction/syscall/crypto assumptions and every other Rc7 row, including L181 rejected-prefix transport, L187 coherent frozen replay and L188 release-wide trust audit. Next deliverable is lead integration of this top/delta alongside concurrent prefix-only workers, followed by those remaining gates. **Target not yet established.**

Stage commits: e4c335d5cf (pins),9566554995 (Result/getters),7d44a3c39c (installed native closure and audits). This handoff is a separate final evidence commit.
