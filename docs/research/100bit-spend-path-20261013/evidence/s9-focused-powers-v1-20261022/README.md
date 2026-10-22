# S9 N=4 power-array semantics

This source-only packet proves a constructive low N=4 powers trace and the high N=4 array returned by the concrete generated `weights.kpowers` operation from canonical seeds. It preserves each returned entry’s indexed power meaning and maps the low trace to the S9 helper carrier.

The theorem is `AspisR1S9N4PowerArraySemanticsV1.actual_s9_n4_low_high_arrays_from_canonical`. It does **not** connect the caller’s reached `ap0` assignment to the constructed low array, and it does not establish Rust `core::array::from_fn` correspondence. The latter remains a separate source-library boundary.

Lean 4.32 focused compile: exit 0, 14.57 s, aggregate peak RSS 3,205,283,840 bytes, process peak RSS 3,228,237,824 bytes, swap 0. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`. Exact selected profile, import closure, command, preflight, receipt, and attempt logs are retained under `evidence/` and `attempts/`. The compiled object is external and not included.

Attempt 1 failed during import-resolution setup; attempt 2 reached the theorem and failed elaboration. Both sources and diagnostics are retained unchanged. Attempt 3 is the accepted green source.
