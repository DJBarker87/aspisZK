# Stage 2 harness plan

No Kani invocation is charged until admitted and actually invoked.
All runs use the unchanged host-run helper, opt-level 3, jobs 4, 6G/8G,
swap 0, TasksMax64; 120-second bounds. Expected work: compilation, then the
named bit-vector/array contract. No finite-field elimination.

Run the scalar row-index contract first, then the three all-variant contracts.
If an all-variant contract times out, the fixed-S1 and fixed-D harnesses isolate
that obligation. They are changed, strictly specialized inputs, never an
unchanged retry. If the all-variant contract passes, its fixed-variant checks
are redundant and will be replaced by independently useful contracts before
charging any remaining run. No stubs, syscall replacements or disabled checks.

Planned exact names (proof-coordinate262/lib.rs):

- `row_index_native_reference`
- `coordinate_m31_all`
- `coordinate_qm31_all`
- `coordinate_wide_all`
- `coordinate_m31_s1`
- `coordinate_m31_d`
- `coordinate_qm31_s1`
- `coordinate_qm31_d`
- `coordinate_wide_s1`
- `coordinate_wide_d`

The coefficient claim is actual `Variant::coefficients(&rows)[position] ==
rows[reference_row::row(variant, position)]`, with arbitrary position <1024,
arbitrary M31/QM31 words and every valid WideExact row (arbitrary limb words
map invalid encodings to zero). Unlike world244, this constructs one output
array and one scalar expected value. A timeout proves nothing. The scalar
row-index claim alone does not prove the coefficient-array association.
