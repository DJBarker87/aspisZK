# Route A evaluation (experimental; complete)

Target not yet established. Nothing in this evaluation adopts a translator, library, generated carrier, source pin, ledger row or contract change. Outputs remain outside main LEAN_PATH. Actual-top premise delta: zero.

## Tools and backend compatibility

Newest published release observed at evaluation start: [nightly-2026.10.27-472b3d5](https://github.com/AeneasVerif/aeneas/releases/tag/nightly-2026.10.27-472b3d5), revision 472b3d560cf236db50f38ad421eb0a88b57a1580, tree 00759c4ce88dc2f315c0306d50bb2987dcbcf953. This is a published prerelease; the stable latest API returns 404. Raw release/tag metadata is retained. Its charon-pin selects 40ca4ab6c10ecb7629320d6eccc0f41423fbe889, tree ac6242433c669bb50c1ed59ab35b5a164de21ae1. Exact per-file source hashes are XRh_new_sourcepins.json.

The upstream backend requires leanprover/lean4:v4.35.0 and Mathlib v4.35.0. It does **not** match the repository's Lean 4.32 pin. No backend compatibility patch or library build is authorized or performed. Matching Charon uses nightly-2026-09-17; the existing pinned Charon uses nightly-2026-06-01. A new MIR frontend/compiler cohort is therefore part of the evaluation and any future provenance comparison.

The newer Aeneas executable built successfully with Dune release profile, j1: SHA256 1ead6274a06d957c188144701c127a90d54b851fb7dce40b1479cc305f6fad00, 52,458,952 bytes. XRh_003 retains the missing host -lzstd linker-name failure; XRh_004 changes only private LIBRARY_PATH and succeeds in 352.430 s, peak RSS 881,936 KiB, swap 0. No translator source patch.

## Probe design

Use five entry-point closures of unmodified retained release bodies: shared-borrow collapse (check_values); Distinct (echeck); context join (checkpoint); borrow/value/marker group (expand_values, wide_view, Dot::push, circle_sample including its closure); Arrow (semantic_boundary). Charon selects the original source bodies and dependencies; no Rust reimplementation or tool-source patch is used. Multiple borrow examples share one Aeneas invocation with normal error collection, so each body must be classified from its own diagnostics. A pass requires the named original body to be present with a real LLBC body and translated without its own error; emission with a failed placeholder is not a pass. If Charon fails before Aeneas, the class remains untested at the Aeneas layer. The shared probe also includes same_batch_index and batch_leaf for common-body scalar/dictionary comparison. A sixth invocation is reserved for the full release tx1 closure, without explicit release opacity, only if probes mostly pass. Backend emission is not Lean verification.

## Pinned route C' result

The untested twelve-leaf input emits complete Types/Funs with pinned tools in XRh_001. See XRh_PINNED-RESULT.md. Part 1 stops on emission. Twelve opaque release-body associations remain open. This is a separate result from the newer-tool experiment.

## Per-class results

All five Charon lowerings exit 0 with has_errors=false; every named original target body is present. Minimal probes retain default dependency opacity, as did the pinned release kit. Inventories list 4/5/2/5/4 opaque dependency functions for shared/Distinct/context/borrow/Arrow respectively. This tests caller translation, not full source refinement. There are no explicit release-leaf opacity selectors.

| Failure class / original body | Newer-tool result | Evidence |
|---|---|---|
| Shared-borrow collapse: check_values | PASS: complete Types/Funs, Aeneas exit 0, 0.615 s | XRh_006; shared_result / inventory_v2 |
| InterpJoinCore.Distinct: echeck | PASS: complete Types/Funs, exit 0, 0.634 s | XRh_007; distinct_result / inventory_v2 |
| Context mismatch: checkpoint | PASS: complete Types/Funs, exit 0, 2.737 s | XRh_008; context_result / inventory_v2 |
| Borrow/value/marker: expand_values | Body and loop translate successfully | XRh_009, normal error collection |
| Borrow/value/marker: wide_view | FAIL: same “There should be no bottoms in the value”, candidate.rs:76–88; newer Interp.ml:682 | XRh_009_errors.txt |
| Borrow/value/marker: Dot::push | Body and loop translate successfully | XRh_009 |
| Borrow/value/marker: circle_sample FnOnce closure | Closure AND circle_sample parent translate successfully | XRh_009 |
| Unsupported Arrow: semantic_boundary | FAIL BEFORE EMISSION: iterator copied signature sanity check, SymbolicToPureTypes.ml:1004–1005; Translate.ml:390. This earlier obstruction does not establish whether pinned Arrow:570 is fixed | XRh_010_errors.txt |

The borrow group exits 1 and emits a **partial** Funs containing a diagnostic `sorry` for wide_view. It is rejected evidence, never imported, compiled or accepted as a theorem. Successful siblings are measured translator emissions only. No generated template axiom is adopted. Six of the eight named body examples translate, but the borrow class as a whole is partial: class tally is three PASS / one PARTIAL / one FAIL.

## Full release extraction

The majority gate (3/5 classes pass) justified the sixth and final newer Aeneas invocation. XRh_011 includes every reached in-repo dependency body (aspis_core, aspis_statement and the three native writer-copy crates), uses NO explicit opaque selector, and leaves std operations to the backend library/digest interface. All 7,978 frozen release source files rehash unchanged.

Charon exits 0 in 75.395 s and emits **dea21e102ce70370a0cba608ca468d02bfc768d535bb977515c168c83e15a432**, 19,227,952 bytes, has_errors=false. Corrected inventory: **915 function declarations, 3,406 call sites, zero missing direct callees, zero opaque project function bodies**. Calls include 34 typed trait-method calls and two dynamic typed function calls; declaration closure is not their concrete semantic interpretation. See XRh_full_inventory_v2.json.

Aeneas exits **2**, 1.677 s, **NO generated files**. Its preprocessing also rejects five bodies before the fatal signature sanity check:

- canonical_scan (candidate.rs:54–73): continue to outer loop unsupported;
- prepared_claim (verifier.rs:53–68): return inside nested loops unsupported;
- state_only_selected_mask_value (state_only_hiding.rs:647–652): return inside nested loops unsupported;
- verify_in_place (multiproof.rs:138–194): break to outer loop unsupported;
- qm31_m31_dot (field.rs:1447): continue to outer loop unsupported.

The later fatal error is the copied/iterator signature sanity check at SymbolicToPureTypes.ml:1004–1005. See XRh_011_errors.txt and full raw stdout. No source/LLBC/tool patch or extra opaque leaf is used to hide any failure. “Full release extraction emits” is **FALSE**. Six newer Aeneas invocations are used; stop, with no retry.

The first evidence inventory parser missed Charon 0.1.299's typed `Value`/`Deduplicated` trait-reference interning and falsely marked 1/3/34 trait calls missing in Distinct/context/full. XRh_012 and v1 inventories are retained as diagnostic history. XRh_013 fixes ONLY the evidence decoder; v2 resolves every referenced trait declaration and reports zero missing calls. This is not a source repair or prover rerun. Use the explicitly named v2 inventories, not v1 counts.

## Measured common-body / carrier / effects comparison

XRh_common_comparison.json and the associated `.lean.txt` excerpts compare the pinned emitted release files with the newer shared probe on the SAME frozen Rust source. The namespaces are deliberately separate; neither is imported.

- `same_batch_index`: **350 bytes, byte-identical** generated definition and source comment; SHA256 9a1c988f1ea47d4362f577c5bae49afd092a2cec7c57d9de487a85ebd8748a28. Carrier spelling remains `Array Std.U32 16#usize`, `Std.Usize`, `Std.U32`, `Result Bool`; it still calls `Array.index_usize` then returns equality. Naming unchanged.
- `batch_leaf`: pinned 2,280 bytes / newer 2,282 bytes. The sole textual difference is `{H : Type}` → `{H : Type _}`. Function, dictionary and method names are unchanged; the digest dictionary still carries `coremarkerCopyInst` and `digest : Self → Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)`. The new generic universe binder and new `@[rust_trait ...]` annotation must be accounted for in a migration.
- New files add Lean's `module`, `public import`, and `@[expose] public section` headers and open `ControlFlow Error`. New loop emission uses `@[rust_loop_body]`, `@[rust_loop]` and ControlFlow loops in the measured probes. This is generated-code evidence, not a transport proof.
- **Textual equality does not imply carrier equality.** In the pinned library, `Result α` is the inductive `ok | fail | div`. The newer `Primitives.lean` defines `Result α := ITree RustEffect α`; failure is a `vis (.fail e) PEmpty.elim`, with separate `ok`, `vis` and `div` definitions. XRh_common_effect.*.lean.txt retains exact excerpts and full library file hashes. Old proofs that case-split on three Result constructors cannot be transferred by name or byte-identical function text. No equivalence for failure/divergence/effect ordering is proved here.

Matching Charon binaries built with `--release --no-default-features --features rustc -j1` (unused MiniRust backend excluded): executable SHA256 **21fe5b0d7c839f328fb934d004d5e7c5397740d8a3255d05598d6b4ec30878c3**, driver **0174aca56a79391deb887b56775b4b82a41ea6006b6e0e95628b3879390953db**. XRh_005 records 424.852 s, peak RSS 2,028,408 KiB, swap 0. Rust compiler is 1.100.0-nightly, commit 923c95cdf5ba65cea505aa2ea829f578e1506ed8, LLVM 23.1.1. Both new tool source trees rehash unchanged after use. Source manifests, binary hashes and native library dependencies are retained in XRh_HostAudit.json. Preserved executable copies are in the private host `XRh_bin/`; no other job or main LEAN_PATH reads them.

## Re-pin work estimate

The measured newer tool is not a drop-in replacement. Both wide_view and the semantic-boundary signature path remain blocked, and strict full closure additionally exposes five control-flow limitations. Resolving those translator/MIR classes comes first; this evaluation cannot bound that effort.

After the blockers are fixed, a rough engineering estimate is:

| Gate | Estimated work, conditional on predecessors |
|---|---|
| Re-emission / provenance | 0.5–2 engineer-days to freeze the new tools/compiler/libraries, re-emit all selected release modules, audit every external and error path, and retain exact source/ELF linkage. The measured ~75 s LLBC lowering is only one command, not this integration work. |
| Carrier/effects/library comparison | 1–3 engineer-weeks for an approved Lean/Mathlib 4.35 migration or a separately reviewed 4.32 compatibility port, including explicit old Result ↔ ITree behavior and restoration/effect transport. This is an estimate, not a proved equivalence or promise. |
| Association re-establishment | At least the original XRg obligation families, now against genuinely emitted carriers. Start with PreparedScratchProjection, then powers/geometry/Dot/candidate/observed-call composition. The inherited per-family estimates (roughly 3–20 focused targets each, overlapping) remain planning inputs; do not sum them into a ledger recount. Many dozens of focused targets and weeks of proof work are plausible; current data does not justify a tighter bound. |
| Closure replay / trust audit | Resolve the actual current top graph afresh, reuse only source/dependency/toolchain-compatible objects, then focused bridges, one axiom/formatter reachability audit and one final coherent replay. Allow several integration days after focused targets pass; compile wall is not measured. Historical Rc7's 4,674-module lower-bound graph is not asserted to be ARX's current closure. A 4.35 migration invalidates 4.32 objects. |

These estimates are inference for the owner's route-A decision. They grant no closure credit and do not add a trust item. Re-establish SAME-execution associations, ownership/cleanup and ordered oracle transport; matching helper outputs or names is insufficient. Historical ELF hashes cannot simply be reassigned to the new extraction.

Recommendation: do not treat today's newer release as ready for adoption. The pinned twelve-leaf emission is now a concrete starting point for the separate association job. The new tool improves several caller translations, but fails strict full extraction and changes the Result/effects foundation. Keep any future translator fix/migration under a separate explicit decision and evidence packet.

## Final scope and resources

1/3 permitted pinned Aeneas invocations used; Part 1 stops on complete emission as instructed. 6/6 newer Aeneas invocations used, plus six matching Charon lowerings. No Lean attempt, Kani run, new top theorem, source adoption or main-path import. #print axioms is N/A for these commands; no standard-axiom proof result is claimed. Types/Funs emission does not prove source association or Lean validity.

The 13 capped scope receipts retain exact commands, source/dependency pins, exit, wall, peak RSS, swap and raw diagnostics. XRh_Verification.json reports no error. One own scope at a time; unchanged S2W runner; MemoryHigh 6G / MemoryMax 8G / MemorySwapMax 0 / TasksMax 64. No cap change, timeout, memory kill, unchanged failed-input retry, reservation retry or bypass. The only build retry changed the private linker environment after a missing -lzstd name. v2 inventory correction is evidence decoding, not tool/proof rerun.

All 7,978 frozen release files, both newer tool source trees and the coherent runner rehash unchanged. Own rebuildable cargo/Dune/dependency caches are removed after preserving executable copies. LLBCs, generated output, logs, tools and source manifests are retained privately; binaries, LLBCs and objects are not committed. No key operation or shipped-file edit; no three-ELF rebuild trigger. Inherited ELF pins are not newly reproduced.

The actual contract top ARX_Root.deployed and inherited Rc10_Top.deployed are byte-identical before/after. Ledger unchanged; atomic-family SAME-witness method, alias L185=L159, delta T0/P0/G0/C0; removed/added/changed 0/0/0. No quantifier, carrier, event, conclusion, security metric or runtime trust item in the adopted theorem changes. Frozen3, approved game and RuntimePersistence retained. No new joint non-vacuity witness is constructed. **Target not yet established.**
