# R117 G augmented-matrix certificate binary

The file is little-endian and contains the original matrix plus the first left-kernel certificate from the `zero-low22` synthetic stress run.

- 17-byte magic: `R117GLEFTKERNEL1\0`
- `u32 rows = 626`, then `u32 columns = 1022`
- 626 × 1022 matrix elements in row-major order
- 626 original RHS elements
- 626 certificate coefficients

Each QM31 element is four little-endian `u32` limbs in order `(c0.a, c0.b, c1.a, c1.b)`. Matrix row groups are: semantic constraints 0–270; raw observations 271–358; point observations 359–361; Final256 observations 362–617; balance row 618; seven relation coefficients rows 619–624; p2 row 625. The first certificate has coefficient `p−1` at row 0 and `1` at row 361, all others zero.

The instrumented Rust execution checked the certificate dot every original matrix column equals zero, and its dot the original RHS is nonzero. The preserved failure occurs after these checks.
