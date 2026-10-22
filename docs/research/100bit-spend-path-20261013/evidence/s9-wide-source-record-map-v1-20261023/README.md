# Wide source record map v1

This focused theorem maps the actual Wide extraction cut’s `mul_by_r` to the actual QM multiplication cut’s `mul_by_r`, preserving all `Result` branches. It also maps the actual Wide `mul_u` body to an explicit formula built from the same QM-cut call. This is a raw source-cut correspondence and does not claim equality with checked CurrentWide arithmetic for noncanonical inputs.

The source compiled with Lean 4.32, standard options, and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Receipt records exit 0, 13.508 seconds, peak aggregate RSS 2,215,149,568 bytes, and zero swap. The import profile is retained for provenance; no compiled objects are included.
