# D381 suspended-row source classification

**Target not yet established. All41 suspensions remain; no row is re-credited.**

Client source classes: {'B': 23, 'D': 15, 'C': 2, 'A': 1}. Across75 distinct matched changed functions: {'A': 46, 'B': 21, 'D': 7, 'C': 1}. A per-function source identity is not a whole-row A certificate.

This is a source-cause audit plus finite deployed-source reruns. **The original standalone structural checker was not recovered for V164, V181, V186, V198, V219, V229, V230, V239, V240, V247, V256, V257, V258, V259.** Each now has a complete reached-source-item guard rejection recorded in closure-guard-results.json and is stopped at source association. The legacy full checker remains unrecovered/D; the guard rejection is not presented as a recovered equivalence proof. No missing gate is counted as passing.

Actual sources and exact complete function diffs are in [functions.json.xz](classification/functions.json.xz), backed by [installed source snapshots](classification/sources.json.xz). Project function spans use the same517-file frozen mirror checked by the original scan and rechecked at cleanup. Resolved dependency sources show zeroize1.8.1/1.9.0, unchanged sha2/digest/block-buffer versions, and the exact GenericArray/typenum feature changes. Metadata, instrumented source prefixes/suffixes, fixture paths and commands are in [captures.json.xz](classification/captures.json.xz).

## Findings and stops

- V170: Deployed Vec Drop uses drop_in_place(slice_from_raw_parts_mut(...)); pinned nightly gate expects raw-pointer cast_slice(...).drop_in_place(). Native260pairs pass; source gate disagrees.
- V178: PathBuf::_push uses inner.truncate(0) and MAIN_SEP_STR; pinned gate expects clear() and MAIN_SEPARATOR_STR. Finite join passes; source gate disagrees.
- V183: Deployed allocator uses NonNull::slice_from_raw_parts and raw_vec layout_array uses Layout::repeat rather than nightly repeat_packed. Source gate disagrees;2160 nativepairs pass.
- V221, V222: zeroize1.8.1 ->1.9.0 replaces scalar compiler_fence(SeqCst) call by optimization_barrier(self). On x86_64/miri=false the selected barrier is readonly inline asm. The original exact volatile-write+SeqCst-compiler-fence trace is not a deployed source association. Native output/destructor checks pass; they do not repair that effect trace.
- V184: Contrary to the example suspicion, actual installed Vec::pop item/body hashes are identical: body66e2c3275af2b6357f4ddc5afa1e9b1e6856c463f6859aa0a8b08b774324a184. Its reached NonNull::cast source differs, so row B; original pop/remove gate and native nonCopy/ZST checks pass.
- V236: Do not promote unchanged root/closure to A: concrete BlockBuffer::digest_blocks was not accounted for by the previous generic-boundary capture.

Stops here are source/gate-association findings. No native value disagreement or privacy counterexample was observed. V221/V222 require a revised source/effect association; an output-only test cannot justify transferring the old fence trace.

## Per-row results

A = lowering only at the entire retained source boundary; B = known std/alloc/core source drift; C = dependency source drift; D = unresolved. B/C can also have unresolved descendants, listed per function in JSON.

| Row | Class | Original structural replay | Deployed finite differential |
|---|---|---|---|
| V164 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | leaves |
| V169 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V170 | B | SOURCE GATE DISAGREEMENT | drop |
| V178 | B | SOURCE GATE DISAGREEMENT | join |
| V181 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | std-extra |
| V182 | B | PASS | append |
| V183 | B | SOURCE GATE DISAGREEMENT | reserve-bootstrap |
| V184 | B | PASS | pop, pop-zst |
| V186 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | std-extra |
| V187 | B | PASS | array |
| V195 | B | PASS | wide-shadow |
| V197 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V198 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | bytes |
| V201 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V212 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V213 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V216 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V217 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | arithmetic |
| V218 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V219 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | leaves |
| V220 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | arithmetic, leaves |
| V221 | C | SOURCE GATE DISAGREEMENT | zeroize, zeroize-drop |
| V222 | C | SOURCE GATE DISAGREEMENT | zeroize, zeroize-drop |
| V229 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | rows-complete-inputs |
| V230 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | arithmetic |
| V231 | B | PASS | sha-snapshot |
| V233 | D | PASS | split |
| V236 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V237 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V238 | B | PASS | ct |
| V239 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | multilinear |
| V240 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | leaves |
| V242 | A | NOT RE-RUN: A, NO RE-CREDIT | NOT RUN |
| V246 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | NOT RUN |
| V247 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | sum |
| V256 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | sampler |
| V257 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | sampler |
| V258 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | weights |
| V259 | B | SOURCE GUARD DISAGREEMENT; ORIGINAL CHECKER UNRECOVERED | weights |
| V260 | D | D: FULL ORIGINAL STRUCTURAL REPLAY UNRESOLVED | weights |
| V265 | D | PASS | circle |

V242 is the only whole-row A classification. Its four pure project bodies are byte-identical in the common source mirror; its MIR storage placement difference remains for the owner. V169 has identical take/replace sources but lacks the concrete Default instantiation census. V236 has identical update/closure sources but lacks the concrete buffer-method cone. Neither is upgraded to A.

## Validation and limits

34/150 new capped native scopes,0/0 Kani verification runs,0/20 Lean attempts; no Env-J ID used. Every scope receipt records exact target, exit, wall time, peakRSS, swap, source revision and axioms N/A. Failed own-input captures remain; corrected runs use changed inputs/environment. No frozen manifest replay was needed or run.

Native reruns use rustc1.94.1, opt3, debug assertions/overflow checks off and unwind as in the client. Project fixtures assert the resolved project-feature sets and retain every crate’s resolved graph. Private snapshot/constructor accessors are appended outside crates/programs to byte-identical source prefixes; no global cfg(kani) is enabled. The reserve fixture uses RUSTC_BOOTSTRAP only for unstable error-kind inspection, recorded separately from deployed implementation/profile. Newly added byte/capacity/compressor corpora are labelled finite validation and distinguished from unchanged historical fixtures.

The conservative reached envelopes are not dynamic call certificates. Macro expansion, concrete dictionary/closure association and unknown target selections remain D where not resolved. Host source/differential evidence does not attest the three SBF ELFs or their1.89 compiler/syscall/ABI behavior. Existing pins remain unchanged.

Before/after endpoint premises: removed0, added0, changed0. Retained: source/executable correspondence, E1/E2, real RunJoin, client route, L1/L2/L3 and exactly entropy_law/entropy_kernel/observation in T. No observer or simulator changed. No keys created or removed.

Next concrete deliverable: replace the rejected source associations with deployed-source laws and recover/rebind the listed legacy structural checkers, resolving their source/model/instantiation boundaries; separately replace the zeroize1.8.1 fence-trace association with a1.9.0 barrier law. Keep all41 suspensions until the lead rules otherwise.
