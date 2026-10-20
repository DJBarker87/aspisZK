# Total five-value geometry array model and actual outer callback body

PROVED: from successful existing geometry/inversion candidate execution and an in-range local query, every actual extracted flat-buffer callback succeeds. In the reused option-free array::from_fn operational model, the five callback calls therefore produce exactly flatInverseArray, in source order, without an independent array-construction-success premise. The whole emitted outer callback body is retained with only the from_fn operation parameterized; the instantiated outer callback succeeds and retains its original flat-buffer capture.

The generic stable callback totality theorem works for arbitrary array lengths using a symbolic fuel induction and checked Usize arithmetic. The existing query decoder's stable-value theorem and standard-operation model are reused; no concrete huge recurrence is evaluated. The production Rust array::from_fn implementation is still a correspondence obligation, not an axiom introduced here.

Four focused NUC Lean owners/five standard-only theorem reports pass at -j1 -M4400, High1GiB/Max2GiB/Swap0. Initial dependency path/import-order errors and small generic proof failures are retained only as diagnostics; no failed source/object is selected. The complete outer-body checker uses the already-pinned raw extraction reference. No production changes or binaries.

OPEN: actual Rust array::from_fn library correspondence; the surrounding Range.map.collect construction of the whole inverse Vec and actual QueryGeometry record; original input/inversion iterator equivalence or adoption, canonical full caller and deployed runtime. The theorem concerns the actual callback body with a checked operational array model and does not close R17 or full 100-bit soundness.
