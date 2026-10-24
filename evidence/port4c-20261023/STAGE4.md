# Concrete std leaves

`Port4C_GeometryStd.install` fixes map_err, slice Iterator::any, Vec::is_empty,
raw M31 equality and zero to their explicit existing TrustedStd-style
interpretations. `any_false` proves the complete symbolic traversal law;
`zero_test_false` derives nonzero for EVERY tested lane. `clone_m31` and
`extend_fields` prove ordered append contents. Domain, prefix, inverse and
field children remain explicit; reciprocal meaning is not claimed here.

`Port4C_QueryStd.install` fixes from_fn to the existing ordered mutable-closure
interpreter. `four_reads` derives the four actual reads in order on the same
opening, using the current closure's [672,800) slice. Decoder op21 remains a
session A backend dependency. This supplies std semantics, not a native P6
runtime/source lowering certificate or complete query arithmetic meaning.

Accepted022/023, exit0, wall3.180293665/2.689417124s,
RSS4424128/4421260KiB,swap0,standard axioms only. Failed geometry006/007/009/
011/013/015–018/020 and query019/021 are excluded elaboration attempts; full
failed sources/errors retained, no failed objects imported. No timeout or
memory kill, no cap increase, no full replay. Standard symbolic induction
replaced the unsuccessful let/coercion simplification tactic path. No huge
numeral or field enumeration was attempted.

Exact section6 fields are in receipts. Budget23/100 Lean at this stage's
accepted targets,0/60 Kani. A subsequent gather attempt024 is excluded and
continues separately. No shipped source/ELF/key/other-worktree change.
