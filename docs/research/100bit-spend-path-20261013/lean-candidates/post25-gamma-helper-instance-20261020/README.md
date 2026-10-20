# Indexed add-small gamma helper refinement (candidate)

This focused Lean owner instantiates the frozen gamma caller's `GammaHelpers` record with the existing indexed low-digit source helper, the candidate indexed `add_small_base_p` entrypoint, and an explicit `decode` function parameter. `candidate_helpers_refine` discharges the caller's low and add refinement contracts; `candidate_gamma_rank_success` applies the existing gamma rank theorem. This is a candidate-source result, not evidence that the indexed add-small candidate has been adopted as production source.

The green proof was compiled on the native Lean 4.32 NUC cache with default elaboration options. The source audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The exact NUC `.olean` is named by hash in the manifest and is not copied into this source/evidence packet.
