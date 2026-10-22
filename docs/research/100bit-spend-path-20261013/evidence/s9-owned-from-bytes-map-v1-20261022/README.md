# S9 owned `from_le_bytes` map

`AspisR1S9OwnedFromBytesMapV1.from_le_bytes_maps` shows the source-shaped owned byte decoder commutes with the parser decoder. It preserves the length branch and ordered byte reads, then reuses the previously proved `from_limbs_maps` theorem on the exact same returned limb array. The result is audited to standard Lean axioms only.

This packet reuses the exact owned `Types`, `Funs`, and `from_limbs` objects from the [from-limbs proof packet](../s9-owned-from-limbs-map-v1-20261022/README.md); those dependencies were not recompiled here. The checker validates their committed receipts and object hashes as well as every direct imported object from this target's launch profile.

`source-identity.json` verifies that the normalized owned `from_le_bytes` and `from_limbs` bodies, and core field structure declarations, match the committed [field decoder source-cut](../s9-candidate-field-decoder-sourcecut-v1-20261022/README.md). This is source-body identity and a Lean translation-level map, not a binary/runtime refinement. No compiled objects are included.
