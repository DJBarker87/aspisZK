# NNJ TX2:217 fidelity controls

Stage 0: controls-only job; no row credit claimed. Target not yet established.

Scope: repair decoder Result<Box<PoolV1PairForestLaneStateV1>,ProgramError> typed arbitrary generation, preserve NMX_shape_* names, then complete Result<(),ProgramError> with mutable [M31;8] assignment controls. Scratch-only cfg(kani) patches; frozen shipped files untouched. Budget 16 Kani / 10 Lean-link-audit / 0 extraction. No new Lean roots, so raw ax2 and print-axioms are not applicable to this job. Existing decoder proof obligations are reused as reviewed by ledger26, never re-credited here.

Rules: AGENTS Security and proof discipline, common/local host rules, C3-BIN (aq),(bf),(bj),(bl),(bm),(bn),(bo),(bp) and owner split-B/Realizes/RZ-STATE. This controls-only authorization requires no extraction or unrelated row work. Preserve frozen graph/lock, deployed features, KMX hash; fresh scope-count/disk/admission before each capped serial scope. No source, trust, metric, privacy or two-transaction changes.

Next: privately seed frozen scratch and original NMX controls, add typed arbitrary implementations in their defining crates (ProgramError is foreign to the harness), then run semantic controls. Every attempted target and actual verdict is recorded, compiler failures never count as negative controls.

## Stage 1 results

Typed cfg(kani) Lane and ProgramError constructors compile in private source/registry copies. Original NMX_shape_stub now fails exactly its caller assertion (NNJ_K001), and its real companion passes(K002). Decoder contract positive K003, modifies violation K004 and actual decoder inverted ensures K005 have expected semantic verdicts. Every run records its frozen graph, deployed features, unchanged lock, exact source patches and section6 fields.

## Stage 2 results and replacement

Actual assignment proof_for_contract K006 PASS, inverted K007 FAIL, real-body caller K008 PASS, empty-modifies K010 FAIL. The arbitrary-index stub K009 and fixed-index stub K012 both timed out90s, with no credit. K011 fixed-index real companion PASS. Digest-postcondition stub shape is retired after two failures, no timeout/cap increase or unchanged retry. The four final Kani slots attempt a separate minimal interface-calibration callee (same full signature/own-input domain/mutable footprint and exact Result carrier), its real/stub companions, then original KMX negative. This does not change or rename the retired callee/harnesses and carries no source semantic credit itself.

NNJ_METHOD.md explains the≤1-byte BorshIoError calibration constructor bound, two-build/body-identity distinction, and exact scopes. No new caller premise or native full-String havoc certificate is introduced. No Lean work beyond the uncompiled recording import; empty new-root audit inventory. All stage changes are committed locally.

## Final controls gate

**Partial: decoder control repaired; assignment calibration remains incomplete. TX2:217 is NOT credited.**

| Shape/control | Attempts | Actual verdict |
|---|---|---|
| Decoder positive / original unimplied real / stub | K003 / K002 / K001 | PASS / PASS / intended assertion FAIL |
| Decoder inverted ensures / modifies | K005 / K004 | intended postcondition FAIL / assignability FAIL |
| Assignment positive / inverted ensures / modifies | K006 / K007 / K010 | PASS / intended postcondition FAIL / assignability FAIL |
| Assignment real at arbitrary / fixed index | K008 / K011 | PASS / PASS |
| Assignment stub at arbitrary / fixed index | K009 / K012 | TIMEOUT90s / TIMEOUT90s; no credit |
| Minimal same-interface contract / real / stub | K013 / K014 / K015 | PASS / PASS / TIMEOUT90s; no credit for stub |
| Exact KMX slice negative | K016 | intended assertion FAIL |

Every attempt's expected/actual result is in NNJ_CONTROLS.json. NNJ_VALIDATION.json independently checks intended failure text (never compiler errors/timeouts), source snapshot hashes, full features, frozen graph, unchanged lock, cgroup limits/admission, compressed-log hashes and unchanged shipped-source pins.13 semantic verdicts validated;3 timeouts explicitly uncredited. NNJ_TIMEOUT_FINDING.md retains all failed shapes and limits the diagnosis. NNJ_CLOSED.json classifies own hypotheses (none added/changed); NNJ_CALLER_CLAUSES.json records the input domains and constructor bound. Decoder exact-tag counterexamples need no String payload; the ProgramError constructor bound is nevertheless explicit and never promoted to universal full-String native havoc. See NNJ_METHOD.md.

## Resource, source and trust accounting

16/16 Kani scopes used,0/10 Lean-link-audit,0/0 extraction. Scope outer wall total449.352189285215s; max process RSS3440360KiB; swaps0. Every scope is serial with host ALL codex-scope count<6, host free≥40GB and fresh reservation exit0 AND allowed:true. MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; fixed harness90s/outer180s. Per-attempt exact target/command/source revision/hash/dependency-feature graph/exit/wall/RSS/swap/print-axioms-N/A is retained. NNJ_TRANSCRIPT.txt gives one-line summaries. Tool pin cargo-kani0.67.0/CBMC6.8.0; frozen lock5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef; CARGO_NET_OFFLINE=true. Kani uses its pinned MIR dev-profile frontend; no heavy debug numerical Rust gate is run.

No new Lean theorem: NNJ_AXIOMS.json has empty raw-ax2/print inventories. NNJ_COMBINED_IMPORT.lean records NMQ_COMBINED_IMPORT with no new modules and is intentionally uncompiled under the controls-only direction. Ledger26's prior candidate closure is reused without another unchanged regression. No Lean cache or Aeneas object is modified/imported, so no selected-object/Aeneas repin is needed. Ten unused Lean slots cannot discharge a missing Kani assertion verdict; no Lean-only obligation remains parked behind Kani.

Only own evidence/prefix files are committed. Scratch `/home/dombarker/project-offloads/codex-cx-tx2-217ctl-20261111` reconstructs frozen source from the archived NMX payload and applies NNJ_HARNESSES.patch plus isolated dependency NNJ_DEPENDENCY.patch. Frozen crates/programs-r1/Cargo.lock remain4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 and Poolb936275465600469312d1f058cdc91ea2a11f3dc byte-identical in the shipped tree. Shared registry originals rehashed unchanged. No source/ELF trigger; inherited pins, NOT rebuilt: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc.

No source/model/caller/row/trust premise is removed or added. Existing P6/D188 native semantic transport stays an option-A reclassification.100-bit PER-ATTEMPT, privacy, two transactions, frozen headline/Realizes/RZ-STATE and runtime items remain unchanged. No headline/security conclusion is established. All16 receipts exist; no owned running scope remains(NNJ_TERMINAL.json). Own cache/source is retained; only owned solver spill files may be removed, recorded in cleanup/retention. No keys/accounts/funds/authority action, sibling/session-A worktree edit or push.

Branch codex/cx-tx2-217ctl-20261107. Plain stage commits; final commit contains this handoff. Next deliverable is exactly NNJ_REMAINING.md's missing assignment stub counterexample, requiring a materially new shape and new Kani budget. The ledger gate decides all row status.
