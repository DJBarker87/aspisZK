# Actual packed-group traversal termination and canonicality

PreweightedLoopCanonical.loop_success proves that the actual generated add_preweighted inclusive-range loop succeeds and preserves canonicality on canonical packed/input arrays with start+N<=96 and end<24. It consumes the concrete checked per-group operation theorem and the retained Aeneas RangeInclusive iterator specification. It does not assume an opaque callback contract or unfold a concrete 24-group computation.

This theorem does not yet identify the full output array with the R0P semantic lane map. The checked per-group value equation and untouched-cell frame are retained separately for the pending exact accumulated-state theorem. Wrapper arithmetic and the enclosing value/terminal caller are separate targets.

Focused NUC Lean4.32, exit0, process swaps0, standard theorem axioms only, explicit4G high/6G max/swap0 cap. Exact source/import pins and complete resource/axiom receipt below.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `PreweightedLoopCanonical` | 1.509 | 3003008 | 1 |
