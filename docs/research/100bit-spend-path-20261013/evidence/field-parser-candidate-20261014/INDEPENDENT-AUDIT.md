# Independent evidence audit

Audited read-only at source base `6e25cda9d35e52df0980dbcd6744522bd3caaab0`. I verified every pre-existing entry in `SHA256SUMS`, the candidate archive SHA/size and all 27 archive-member hashes from `manifest.json`, and byte equality of the materialized generated files and patch to their archived copies.

The pinned repository `field.rs` at this base hashes to `3046536d04e84357c7df7bd742ec9839d1e1dc47ccc0ecaa59eb79ddec453c68`. The retained patch hashes to `f048cad49748468db3b1732b1a1e7f74560a8a029c7b0b1c5815912b92a87ac5`; applying it to that pinned source reproduces candidate hash `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea` exactly. The Charon extraction and Aeneas translation receipts both report exit 0 (1.774 s total, peak RSS 306768 KiB, swap 0, 4G/6G/0 scope). The standalone raw generated files were not compiled directly in this extraction layout. The corresponding retained declarations with pinned Option support are covered by seven green Lean targets in the sibling `lean-candidate-field-parsers-20261014` bundle.

This verifies artifact identity and the recorded generation run only; it does not establish a Rust-to-Lean refinement theorem.
