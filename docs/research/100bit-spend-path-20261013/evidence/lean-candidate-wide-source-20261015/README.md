# Candidate Wide parser retained-source compile

`R1CandidateWideParserSource` compiled successfully under the pinned 4G/6G/0-swap NUC runner. The compiled file imports only `R1CandidateFieldParsers`, reuses its exact shared field and Option declarations, and adds the four declarations checked by `tools/retain-wide-parser.py`. That checker passed before the compile: three shared types, six shared function/global declarations, four new declarations, and seven nonopaque functions in the extraction metadata.

The target is the isolated candidate generated from an input that changes only `WideExact::from_le_bytes`. This is source retention plus a focused Lean compile; generated Lean source was not refined against the Rust compiler and no runtime or SBF gate was run.

The exact compile snapshot, source hash sidecar, receipt, full Lean output, time log, final `.olean`, compiler runner/environment, retention checker, and source pins are retained here. The imported `R1CandidateFieldParsers` source/object are referenced from the earlier [candidate field parser evidence](../lean-candidate-field-parsers-20261014/); its source SHA-256 is `8d5bd9a6…e4531` and the pinned object SHA-256 is `38c006c6…b5fdc3`.

Axiom output: the `WideExact` structure has no axioms; its `BYTE_LEN`, `from_le_bytes`, and `parse_wide_exact_probe` report `[propext, Classical.choice, Quot.sound]`.
