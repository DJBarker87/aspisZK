# Actual parser validates the same returned 224-byte round-one slice

`AspisR1ViewParseProbe.ParseSuccessRound1Length.parse_success_round1_length` proves that successful execution of the parameterized generated candidate parser, with the two-fold returned variant, implies both successful non-initial `echeck` on the exact returned `view.round1` and length224 for that same slice. The query checker is universal and its success is not supplied as a premise.

The endpoint derives the successful `parse_shape` result, returned variant identity and exact checked range-index equation from the parent source flow. A separate focused proof follows actual shape parsing and shows the true folded-offset branch has round1 interval width224. The checked slice-index lemma derives the returned slice length from successful indexing. The proof therefore binds validation and length to one returned source slice rather than independently chosen byte arrays.

The old successful echeck-to-seven-canonical-chunks and strict second-record codec proofs are the next consumer. The H-to-retained-parser carrier adapter, folded-root identity and final actual-record framing remain open; this checkpoint does not claim they are discharged. Candidate-to-release source migration and deployed artifact correspondence also remain separate.

Dotted module paths now match the imports in the final theorem. Exact already-green FoldedOffsetsWidth source/object was reused under the required namespace path, with its original target receipt retained and its object pinned by consuming imports. The other required module-path builds likewise retain exact source hashes and their focused import receipts. No unchanged broad replay was run.

All focused checks exited0 on the NUC with zero process swaps under explicit memory/swap caps. Every theorem axiom report contains only `propext`, `Classical.choice` and `Quot.sound`. Exact source/import/revision/object pins, command/resource receipts and axiom output are retained below. No complete accepted-spend soundness or privacy result is claimed.

| Module | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `AspisR1ViewParseProbe.ParseSuccessRound1Index` | 1.92 | 2673188 | 1 |
| `AspisR1ViewParseProbe.SliceIndexLength` | 1.287 | 2635432 | 1 |
| `AspisR1ViewParseProbe.FoldedOffsetsWidth` | 1.311 | 2637652 | 1 |
| `AspisR1ViewParseProbe.ParseShapeRound1Span` | 1.472 | 2648484 | 1 |
| `AspisR1ViewParseProbe.ParseSuccessRound1Length` | 1.243 | 2631640 | 1 |
