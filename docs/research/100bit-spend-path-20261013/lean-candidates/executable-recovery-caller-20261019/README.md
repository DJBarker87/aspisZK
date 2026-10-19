# Executable recovery caller candidate snapshot (2026-10-19)

**Pending end-to-end joint caller.** This directory is a candidate-source snapshot, not the canonical `lean/` tree and not a complete release claim. The final-only path through computable distance filtering and actual-message recovery is green on NUC Lean 4.32. The initial runtime evaluator/recovery and the generic executable joint-list merge are also green. The wrapper instantiates that merge with `initialRuntimeEncoder` over `List.finRange 29`, proving output length at most 100 and exact refinement to `ConcreteBinding.candidates` under the per-lane close-completeness premise. It does not yet discharge that premise from the final fixed-input bank caller.

Each source has an exact SHA, direct imports, and status in `source-manifest.json`. Receipts and time logs for the new green leaves are under `evidence/`.

## Dependency order

Follow `source-manifest.json` `dependency_order`: fixed-input decoder family and literal constructors; root candidate contract; GRS bridge and interpolation agreement; final filter, runtime distance evaluator, and actual-message recovery; then initial filter, runtime evaluator, actual-message recovery, generic joint merge, and the concrete lane-order wrapper. The second-fold sparse projection core is a green prerequisite; its final-five-lane caller remains pending.

## Remaining obligations

- Discharge every initial lane’s close-completeness premise from the actual fixed-input bank result using the valid interpolation witness and candidate-list theorem.
- Connect the returned joint list to the terminal witness extractor and prove the actual caller’s list bound and completeness with the same candidate set.
- Compile the final-five-lane sparse projection caller. It must retain separate channel words and use each channel’s successful decoder output; no equality assumption between the four words is available.
- Run only the focused remaining bridges, then the final frozen integration checks. This packet does not establish end-to-end extractor completeness or release readiness.
