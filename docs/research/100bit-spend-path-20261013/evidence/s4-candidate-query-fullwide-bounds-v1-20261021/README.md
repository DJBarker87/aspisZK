# S4 candidate query FullWide coordinate bounds

This focused source-only packet lifts the existing candidate-query output evidence to explicit field-coordinate bounds on the actual Stage2 `FullWide` values. `current_wide_to_full_preserves_canonical` unfolds the selected Current canonical predicate and follows the fieldwise carrier map; `current_array_to_full_preserves_canonical` lifts it over the mapped array. `candidate_query_fullwide_coordinate_bounds` consumes the existing `CandidateQueryFieldEvidence` and retains the same reached query and returned candidate array together with eight U32 bounds, each `< 2147483647`.

No scalar premises were added. The result remains at the candidate query / Stage2 model boundary; it does not close the Rust Std or runtime correspondence.

Validation used the pinned Lean 4.32 binary, `-j1 -M 4400`, and the selected warm import profile recorded in `receipts/command.json`. Exit status was 0, wall time 19.20 s, peak RSS 3,986,685,952 bytes, swap 0. The fieldwise scalar theorem has no axioms; the array theorem reports `[propext, Classical.choice, Quot.sound]`.
