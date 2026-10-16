# Actual add_preweighted per-group arithmetic

PreweightedClosureSuccess proves the exact generated closure succeeds with checked index arithmetic and selects the correct lane or zero padding (group<24, slot<4, start+N<=96). PreweightedLaneArray uses the retained ArrayFromFnCopyStable theorem to prove all four constructed cells have that exact value and are canonical when input lanes are canonical. PreweightedGroupArithmetic composes this actual source construction with the retained generated qm31_pack_base4 correctness proof and actual checked QM31 addition: the result is canonical and decodes to old + mathematicalPack of the four selected lanes.

The exact source declaration slice comes from the archived indexed terminal candidate. Its bodies are unchanged except enclosing namespace isolation. This batch does not prove the outer add_preweighted inclusive-range traversal, the complete add_value_lanes caller or the full terminal implication. No new opaque callback contract is assumed.

Each smallest changed file passed a focused Lean4.32 NUC check under4G high/6G max/swap0; all exits0, process swaps0, theorem axiom reports standard only. The source slice contains declarations only. Receipts preserve exact source/import pins, wall time, RSS and axioms.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `PreweightedClosureSlice` | 1.292 | 2597576 | 0 |
| `PreweightedClosureSuccess` | 1.702 | 2615040 | 1 |
| `PreweightedLaneArray` | 1.439 | 2989580 | 2 |
| `PreweightedGroupArithmetic` | 1.401 | 2993948 | 1 |
