# NDO reconciliation

## Nonidentical sources first

The two forests are **not an import-only byte renaming**. Of 2,922 historical/replay pairs, 70 differ after exact import-token replacement. 47 differ only in comments/whitespace; 23 have phase/observer changes. `NDO_DUPLICATES.json` puts every nonidentical pair first and records both source and predecessor object hashes. `NDO_SOURCE_DIFFS.txt` retains every difference.

`S1SemanticPhaseV1` formerly exported `AspisR1PublicPreparation.verifier.Phase := FirstCaller.Phase`. Its replay replacement exports no such alias and imports `RPz7_PhaseIso`, which retains the old S1 carrier as `RPz7_PhaseIso.Phase`. The selected emitted producer owns a nominally distinct `verifier.Phase`. The other 22 substantive differences change observer argument types to the retained carrier; `FIr_FinishComparison` additionally transports producer observers with `observerToFirst` at its FinishModel call and proof application. `RPz7_PhaseIso` supplies explicit variant-preserving bijections, callback/observer/consumer round trips and evaluation lemmas. These are existing source transports, not permission to identify the nominal carriers silently. Arbitrary callbacks and adaptive execution cannot be transferred by acceptance equality. Release `none` observers still require their concrete selected-call/type checks.

The full list of 23 changed bodies is in the JSON (`body_equal_ignoring_comments_whitespace_imports=false`). No new equivalence or cryptographic discharge is claimed here. The frozen Rust source, headline and release contract are unchanged.

## Inventory and provenance

The predecessor graphs contain 12,712 headline and 15,068 witness modules. Name matching includes RPx/RPv/RPu/RPt/RPz8/RPz7/RPz4/RPz prefixes and flattened dotted module names. Exact comparisons preserve all bytes except complete import tokens. A separate weaker comparison identifies formatting-only differences; it is not substituted for byte identity.

2,846 available source/provenance hashes were checked against historical candidates (some modules have both checks). 76 historical pair entries have no available source pin in the inspected predecessor manifest and no currently available source file in its cache record. Those entries retain explicit repository source paths/hashes and object hashes, but their source-to-object provenance is unverified. The two available host sources differing from the current repository (`Op5T_Final`, `Op5T_SuccessAccepted`) are retained as text and used for the comparison; their differences are comments only. Source hashes do not by themselves certify compiled-object provenance.

## Retargeting plan and budget

`NDO_RETARGET_PLAN.json` gives dependency-first ordering for 3,118 affected witness modules after substituting all 2,922 pairs. This is substantially larger than the authorized 60 normal Lean attempts. Existing compatible headline modules are reused directly; no arithmetic certificate is intentionally recomputed. Only task-owned source/cache paths may be written. Both predecessor caches remain read-only, and the task cache is retained.

Status: stage 1 inventory complete at source-comparison level, with the 76 source-provenance qualifications above. Stages 2 and 3 are pending. No Lean invocation or final combined replay yet. Target not yet established; release obligations 1 and 4 remain open.

Stage 2 source preparation: all 3,118 NDO_ copies now exist under `lean/`. `NDO_RETARGET_SOURCES.json` pins each historical source and generated source. Every non-import byte is preserved, except the requested root namespace becomes `AspisR1.NDO_Joint`. Source imports exactly match the mapped predecessor dependency graph (zero discrepancies). A source scan rejects new axioms, opaque declarations, sorry/admit/native_decide. These are **prepared sources, not 3,118 passing proofs**. The 17 sources missing from predecessor source records use existing repository Lean sources, explicitly recorded in the source manifest.
