# S4 candidate-backed preparation powers bridge

This source-only packet proves a candidate-model variant of the prepared-scratch/query bridge. A single successful `prepare (concreteBoundaries (withCandidateSamplers sampling))` run yields both canonicality of the returned gamma and the exact `ClaimPowers.powers 29` output equal to the returned scratch array. The ten-query field-result theorem then consumes that same scratch array after its explicit carrier conversion.

The model uses the existing indexed `early_powers` candidate underlying `ClaimPowers`; it does not use `sourceBoundaries` or the Rust Std/from_fn powers model. This removes that Std boundary from this candidate theorem. It does not prove that the candidate equals frozen `weights::powers`, and it does not bind the frozen tx1 parent caller to this theorem. Those remain separate open source-equivalence obligations.

The final Lean 4.32.0 check exited 0 in 15.459 s (peak aggregate RSS 3,918,774,272 bytes; peak process RSS 3,941,875,712 bytes; process swaps 0). The three declarations report only `[propext, Classical.choice, Quot.sound]`. Exact target/source/object pins and direct import object hashes are in `manifest.json` and `evidence/`. The recursive import closure is retained as provenance, not copied compiled objects.
