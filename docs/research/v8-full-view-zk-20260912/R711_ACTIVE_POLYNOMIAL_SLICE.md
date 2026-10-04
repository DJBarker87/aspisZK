# R711: Active polynomial slice identity

This target connects the selected active polynomial minor to the full active matrix determinant along the reciprocal slice `u · u⁻¹ = 1`. It proves an algebraic identity only; no challenge distribution is included.

Canonical Lean target: `AspisV8R19/R711ActivePolynomialSlice.lean`, SHA-256 `548557932cad685f79de750cad17dc2067bee88101e2d026d48235aecb35e8da`. Source revision: `16aca98195bde6dd82aa6ea453fc29da0cc449c7`. Green focused run `1791128852410946000`: exit 0, wall 1.36 s, peak Lean-child RSS 3,274,216 KiB, swap 0, with Lean 4.32, `-j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.

`column_at_one` binds the selected active channels to the source-shaped columns at `alpha=1`; `sourceMinor_one` identifies the corresponding source minor with evaluation of `fullMatrix`; and for `u ≠ 0`, `determinant_slice` proves

```lean
MvPolynomial.eval (activeAssignment 1 u u⁻¹) (polyMinor half).det =
  (fullMatrix half).det.eval (-(u + u⁻¹))
```

All three complete `#print axioms` outputs contain only `[propext, Classical.choice, Quot.sound]`.

The successful receipt directly pins R709 SHA-256 `3cb21ea43a79427e13068c3e46a2de197623c2c4b3eb80c49d922d9ba88e7422` and R710 SHA-256 `cff02943fe6b61f2ffde5c45425c325ec91d60b5be9ad9c7807bff95fba2a454`. R710 transitively imports R707, SHA-256 `3369c8638dda2132231ad174d6bcfa5f0c126c3a3fc2fbbe41c9d8445f891d9a`. R709 was promoted after the R711 compile; its canonical source now matches the manually supplied import pin.

The complete source snapshot, run log, receipt, and runner are preserved in `evidence/r711-active-polynomial-slice/`. This proves the reciprocal-slice determinant identity for nonzero `u`; it does not prove the determinant polynomial is nonzero at an admissible sampled pair, any challenge law or retry loss, native source execution, or privacy/security closure.
