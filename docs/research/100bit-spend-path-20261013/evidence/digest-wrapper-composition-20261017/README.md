# Whole bounded digest wrapper composition

`AspisR1.DigestWrapperComposition.wrapper_eq_factored` proves the complete bounded-carry wrapper Result equals the original-source prefix, actual outer loop and proved source suffix. Recipient presence is split explicitly to preserve the complete do-block behavior. The returned snapshot from the actual loop is used by the suffix; it is not silently replaced by the caller input.

`source_success_of_outer` then derives successful canonical output and equality to the original entire `R0P.publicDigestLanes`, from the same public/openings/boxed selector and canonical input words, GIVEN the explicit `OuterSound` premise. That premise requires actual twenty-level source execution to return the canonical accumulated digest and the same snapshot, with every output cell matching the symbolic frontier model. It has NOT been assumed true or discharged in this commit: the independent outer-loop execution proof must instantiate it. There are no additional hidden middle-stage success assumptions.

The typechecked wrapper is an explicit implementation model candidate following the committed Rust bounded-control patch. It replaces the unsupported generated trailing_ones/cast/min fragment with the actual extracted and universally proved bounded_carry call. The model edit and generator record that full modified-crate re-extraction and release/runtime correspondence remain open. The original pre-edit full model is retained as an input artifact only; its unsupported std intrinsic was not compiled or introduced as an axiom.

Both focused NUC checks exited0 under 4/6 GiB cgroup limits and swap disabled, with no dependency rebuild. The two whole-wrapper theorem audits contain only standard axioms. Exact source/object/import pins, commands, source revisions, timing, RSS and swap records are retained. This is a conditional component theorem, not a completed accepted-spend, privacy or 100-bit release proof. No complete frozen-manifest replay was run.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `DigestWrapperBoundedSource` | 1.782 | 4036860 | 0 |
| `DigestWrapperComposition` | 1.788 | 4058428 | 2 |
