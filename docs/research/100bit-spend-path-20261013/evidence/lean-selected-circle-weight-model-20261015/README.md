# Selected circle-weight model evidence

This bundle records the focused green compile of `R1SelectedCircleWeightModel` attempt b and failed attempt a. The active proof imports the current `AspisFormal.V5FriNaturalBasisRadix4` module, which transitively uses `CircleNaturalBasisEval`; hashes and the compiled objects are pinned above.

The old `SourceEncodedOpening.circleWeight` / `CircleWeightBridge.circle_four` files are pinned as formula provenance only and were not imported by this target. The checked result establishes a pure coefficient-model identity and does not establish Rust source refinement.

Attempt b: exit 0, 1.24 s, peak RSS 2,190,108 KiB, swap 0; axioms `[propext, Classical.choice, Quot.sound]`. Attempt a failed because `Mathlib.Tactic.Omega` does not exist in the pinned environment.

Object-storage note: the canonical compiled objects are the byte-identical members of `compiled-objects.tar.gz` listed in the manifest. Loose duplicate `.olean` files were moved outside the bundle to `/tmp/aspis-r1-retained-loose-objects-20261015/lean-selected-circle-weight-model-20261015/`; archive members and object SHA-256 pins were not changed.
