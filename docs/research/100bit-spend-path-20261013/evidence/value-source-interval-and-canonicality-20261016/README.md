# Source value packing and preprocessing canonicality

ValueLaneIntervalJoin proves symbolic concatenation of two contiguous zero-padded finite-vector intervals. ValueLaneSourceVector identifies actual QM31 source lane selection, after the checked field embedding, with that vector selection. It composes the actual start49/33-cell and start82/two-cell packing calls into a single 35-cell interval, proving source success and canonical output from canonical inputs.

ValueLaneResidualList transports that source result to an ordered residual list. Its final valueFamily theorem keeps one explicit residual-list identification premise, to be discharged by the ongoing source construction proofs. This premise is not claimed closed.

The exact generated preprocessing loop slice is retained with its source provenance. Loop0/1/2CanonicalOpenings prove that successful actual loops preserve the unchanged openings and canonical range arrays. PreprocessCanonical composes them; ZeroInit proves canonicality of the actual repeated-zero initializer. These are preservation results conditional on the actual loop-result equations; unconditional loop execution and exact decoded range values are the next dependent targets, not implied by canonicality alone.

The focused Lean4.32 checks ran on the NUC under explicit memory/swap caps, with zero process swaps. The checked theorem reports contain only propext, Classical.choice and Quot.sound; the generated slice has no theorem reports. Exact source and direct-import pins, commands, timing/RSS, reservations and axiom output are retained. No whole-package replay or new external axiom is introduced. End-to-end source soundness, extraction, privacy and release/runtime gates remain separate.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `ValueLaneIntervalJoin` | 1.918 | 4051612 | 2 |
| `ValueLaneSourceVector` | 2.342 | 4062184 | 2 |
| `ValueLaneResidualList` | 2.716 | 4057060 | 4 |
| `SelectorValueLaneLoops012Slice` | 1.346 | 2608624 | 0 |
| `SelectorValueLaneLoop0CanonicalOpenings` | 1.633 | 3005792 | 2 |
| `SelectorValueLaneLoop1CanonicalOpenings` | 1.756 | 3007472 | 2 |
| `SelectorValueLaneLoop2CanonicalOpenings` | 1.787 | 3007556 | 2 |
| `SelectorValueLanePreprocessCanonical` | 1.347 | 2993840 | 1 |
| `SelectorValueLanePreprocessZeroInit` | 1.341 | 2991588 | 2 |
