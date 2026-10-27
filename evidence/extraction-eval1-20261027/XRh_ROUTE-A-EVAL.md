# Route A evaluation (experimental; in progress)

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

Pending tool builds and invocations. Do not infer success from this scope document.

## Re-pin work estimate

Even if the newer probes pass, re-pin work has four dependent gates: re-emit and inventory the entire call-closed frozen release (including every error/external and rejected prefix); compare carriers, dictionaries, Result/effect behavior, naming and restoration continuations; re-establish concrete SAME-execution source associations/P6 and ordered oracle transport against those actual carriers; rebuild the actual headline dependency closure with axiom/formatter reachability audits and frozen source/ELF correspondence. Upstream Lean/Mathlib 4.35 also entails either a separate approved migration or a separately reviewed 4.32 compatibility port. Historical 4.32 objects cannot be claimed valid for 4.35 outputs. These are engineering/proof obligations, not a new cryptographic assumption. Quantitative estimates will be qualified by the measured probe results; no adoption recommendation is made before them.
