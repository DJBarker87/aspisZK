# R595 full G-core chord scaling

R595 proves generic algebra for the 271×271 `R574SparseGCorePolynomial.coreMatrix`. Scaling every chord coordinate `(a,b,c)` by `scale` scales each `coreMap` result and each matrix entry by `scale`; consequently the determinant is multiplied by `scale^271`. When `scale ≠ 0`, the scaled and unscaled determinants are nonzero together.

The proof uses R574’s `sourceChord_components`, the matrix definition, and `Matrix.det_smul`; it does not unfold the generated source recurrence. It makes no claim that the selected verifier’s `R203` chord values or actual transcript parameters instantiate these algebraic variables. The source-to-model normalization and challenge-law obligations remain separate.

## Verification record

- Canonical target: `AspisV8R19/R595CoreChordScaling.lean`.
- Source SHA256: `480a217c303ceb06770e2037088e19a77a7d9d9156f00668fec527c6db91e546`.
- Source revision at green compile: `fbe0fbefa117198c80496267d11e4077d7f13bf2`.
- Focused compile: exit 0; run `1791089062188069000`; wall 0.96 s; peak RSS 2,248,312 KiB; swap 0.
- Pinned Lean 4.32 cached workspace, `-j1 -M4500`, systemd scope `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.
- Direct import `R574SparseGCorePolynomial.lean` SHA256: `ccd4bab7796221eada233ba04de5c83a09e8565f69009d24115d7a822abc4b16`.
- Complete `#print axioms` output for `coreMap_chord_scale`, `coreMatrix_chord_scale`, `coreMatrix_det_chord_scale`, and `coreMatrix_det_ne_zero_iff_chord_scale`: each depends only on `[propext, Classical.choice, Quot.sound]`.

Evidence preserves both the failed and successful source snapshots, logs, receipts, runner, imported source, and SHA256 manifest. The failed attempt tried to rewrite matrix entries after `ext`; the corrected proof changed the goal directly to the equivalent core-map equality. No benchmark, broad regression, or actual-source run was performed.
