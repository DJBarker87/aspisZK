# Candidate WideExact parser refinement evidence

This focused bundle records `R1CandidateWideParserRefinement` attempt `wide-refinement-a` (failed proof elaboration) and `wide-refinement-b` (green). The green source proves `wrong_length` and `source_refines` for the isolated Aeneas WideExact parser model, reusing pinned candidate QM31 parser and strict two-half byte-codec modules. Its `#print axioms` reports for both public theorems contain only `propext`, `Classical.choice`, and `Quot.sound`.

The exact source snapshots, receipts, sidecars, logs and time logs are retained under `attempts/`. `objects.tar.gz` contains only the green target `.olean`; imported modules are source-pinned and their compiled object hashes are recorded in `source-manifest.json`. Runner and environment snapshots are under `runner/`. No Lean target was rerun during collection.

This is a formal result about the isolated candidate model and its direct imports. It does not establish that the candidate bytes match the current Rust parser, or connect `View::parse`, checkpoint resumption, or caller behavior to the model. `source-manifest.json` records the inspected source base and all relevant hashes.
