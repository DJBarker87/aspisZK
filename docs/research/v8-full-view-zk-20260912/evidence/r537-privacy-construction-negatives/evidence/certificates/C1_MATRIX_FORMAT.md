# C1 initial-mask-preservation certificate binary

The saved `c1-left-kernel-col0.bin` is little-endian:

- 18-byte magic: `R117C1LEFTKERNEL1\0`
- `u32 equations = 112`, then `u32 variables = 221`
- 112 × 221 original M31 matrix entries in row-major order
- 112 original M31 right-hand-side entries
- 112 left-kernel coefficients

Each M31 element is a little-endian `u32` in `[0, 2147483647)`. Rows 0–87 are four-slot raw queries; 88–99 are the three point claims, four QM31 limbs each; 100–107 are the two OOD claims, four limbs each; 108–111 are the exact source initial-mask contribution, four limbs. Variables are legal relation-free mask cells for C1 column 0, omitting dependent row 1023 and the existing `(column=3,row=1014)` exception (not applicable to this column).

The certificate has the single nonzero coefficient `row 108 = 1`. The instrumented Rust run and an independent local M31 check verified its dot with all 221 original matrix columns is zero and its dot with the original RHS is `2147483646` (`p−1`). The run preserves the original incompatibility panic.
