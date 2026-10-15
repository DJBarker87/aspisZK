# NoteHashMap focused Lean evidence

This bundle records ring-hom naturality of the generic R0 sponge and note hash
functions and the 24-level Merkle path. It composes the existing symbolic
Poseidon permutation and node-compression transport lemmas; it does not
evaluate rounds or unfold the 24-level recurrence, and makes no runtime or
Rust refinement claim.

Final target `R1NoteHashMap`, attempt `note-hash-map-d`: exit 0, wall time
2.68 s, peak RSS 3,339,296 KiB, swap 0. The target used the pinned capped
4 GiB high / 6 GiB max / 0 swap / 128-task runner. All ten public axiom audits
report `[propext, Classical.choice, Quot.sound]`, inherited through the
existing `PoseidonMap` naturality. Attempts a–c are preserved as failed
proof-plumbing attempts with exact sources and raw receipts/logs.
