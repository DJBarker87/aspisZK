# S4 callback head batch coordinates, v1

This focused theorem starts from one successful emitted callback call under an explicit model adapter: `ActualBatchOps`, the reviewed P6 N4/N8 array execution, and the checked EbyK `from_limbs` implementation. It extracts the *same call's* base-loop accumulator and N8 array output, converts the callback iterator to the exact outer-loop schedule, and invokes the seven-batch source trace/residue theorem on those values.

The result retains the `ExactTrace` and its parsed contributions. The returned `values.val.map U32.val` is exactly the ordered vector of eight `fullSum (rawBatchLists trace coordinate) % modulus` values, and the same callback body is exactly `finishToCurrent (wideFromParts word0 ... word7)`. Thus the eight packed coordinates are those same source-product residues. All 29 coordinate-bound facts remain explicit as `hcoords`.

The packet does not establish the Rust standard-library `array::from_fn` operational correspondence or prove that production installs these model Ops. It is a source-model composition, not a complete production callback or security theorem. The raw callback's successful base loop and N8 array execution are not independent premises: both are extracted from the single callback success hypothesis.

The successful target is axiom-audited to `[propext, Classical.choice, Quot.sound]`. Attempts v1 and v2 are retained under `diagnostics/` as rejected proof-development records; only v3 is selected. `source_owner_pins.json` records the exact source/object owners selected from the launch-time LEAN_PATH; copied dependency sources are snapshots and their producer packet references are listed in the manifest.
