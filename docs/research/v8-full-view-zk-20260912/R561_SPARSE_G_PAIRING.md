# R561 — sparse G pairing

## Verified result

[`R561SparseGPairing.lean`](lean/AspisV8R19/R561SparseGPairing.lean) is the
canonical copy of the focused target that compiled in run
`1791075464264831000`. It proves the complete sparse-G pairing identity over
an arbitrary field:

\[
  \sum_{r : \mathrm{Fin}\ 1024} \mathrm{original}(w)(r)m(r)
  = \sum_{i : \mathrm{Fin}\ 271} w(i)m(\mathrm{order}(\mathrm{coinIndex}(i))).
\]

The proof uses the exact selected field-model scatter position
`order (128 + 3*i)` through `TwoSwapSourceG.coinIndex` and
`TwoSwapSourceG.original`. It then specializes `w` to
`maskWeights271 half z` and rewrites the resulting dot product through the
existing `maskWeights271_dot` / `sourceMaskLoop` result. It does not use
the dense source-mixing construction.

## Evidence

- Canonical target SHA-256: `2fa3fc771ac16e2512ac0bea523beae3b2d5b1afb0d892bf66a41c02f80d386c`
- Campaign source revision: `2a53ea51fa562639281de5c2e7ffa982d6146699`
- Final status: exit 0; wall 1.04 s; peak Lean-child RSS 2,306,540 KiB; swap 0.
- Scope: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`,
  `TasksMax=128`, Lean `-j1 -M4500`.
- Complete final axiom reports are retained in
  [evidence/r561-sparse-g-pairing](evidence/r561-sparse-g-pairing), with only
  `propext`, `Classical.choice`, and `Quot.sound` reported.

The evidence directory contains the exact green source, full raw log and
receipt, checksums, all three failed R561 attempts, and the focused direct
`MaskSourceSlices` dependency build. The first attempt stopped before
elaboration because that cache dependency was absent; it is retained rather
than replayed.

## Boundary

This is a field-model identity for the named sparse representation. It does
not establish native Rust scatter writes or wrapping arithmetic, correspondence
between Rust execution and this model, image or rank coverage, oracle/query
behavior, privacy, soundness, or an end-to-end security claim. The first
remaining proof boundary is actual selected sparse-scatter execution and its
connection to this representation.

## Direct import pins

The final focused receipt records these exact direct local imports:

- `AspisV8R19.TwoSwapSourceG`: SHA-256
  `4a09c5bdb945fb7d7c7b46a3c19d89d5d293973e8977337ff2e9603bb2491ee5`.
- `AspisV8R17.MaskSourceSlices`: SHA-256
  `7ab54d46a1f4d576714390d9ea2c04a92ec0f7aa859abcb3d4fad9d03a679389`.

The canonical target is byte-identical to the saved green source.
