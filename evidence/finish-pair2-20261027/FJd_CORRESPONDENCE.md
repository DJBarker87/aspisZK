# P6 reference correspondence (pending proof gates)

No named P6 equality is an axiom or a newly approved trust item. Kani receipts
and source-to-Lean correspondence must both be present before installation.
Reference algebra alone receives no deployed premise-removal credit.

| Shipped source | Safe reference | Lean reference | Bounds / SAME operands |
|---|---|---|---|
| Weights::new point loop, weights.rs 209-212 | point_factors | FJd_PointReference.factors/pointFactors | k0 first, d0..5; original alpha, TAU unchanged |
| Weights::tensor, weights.rs 240-252 | tensor_reference | planned tensor64 | folds2, d2..5; 64 outputs, same factors |
| state_only_statement_points, state_only_prefix.rs 600-612 | successor_reference | planned reverse fold | original ten coordinates; carry starts ONE; reverse order |
| Weights::new circle loop, weights.rs 214-220 | circle_reference | planned four-step fold | both original z endpoints; d1..5; x initial double(z.x) |
| EbyKDot::push/finish, fast_pairing.rs 159-187 | dot_reference | planned left fold | 64 same canonical E/K values; no stubs |

The harness extraction is a byte-exact weights.rs prefix followed only by a
cfg(kani) child module declaration. No shipped path is edited. The standalone
harness reuses the read-only host source corpus for its aspis dependencies.
This extraction needs an explicit source hash audit; Rust equality does not
itself establish Aeneas/Lean correspondence or model tensorPoint transport.
