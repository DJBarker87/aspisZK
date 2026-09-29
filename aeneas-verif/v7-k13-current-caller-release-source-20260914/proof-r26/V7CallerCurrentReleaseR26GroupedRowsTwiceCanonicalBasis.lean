import V7CallerCurrentReleaseR26GroupedRowsTwiceBasis
import V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3Evaluation

/-! # Canonical tensor basis for the fused grouped fold

This packages the basis built by the extracted helper as sixteen canonical
field values.  The nine cross terms are constructed through the already
verified source multiplication bridge, so later chunk proofs can use them
without reducing the generated `array::from_fn` computation.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalBasis

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26GroupedRowsTwiceTrace
open V7CallerCurrentReleaseR26GroupedRowsTwiceBasis
open V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0
open V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalOps

abbrev RawQM31 := field.QM31

structure CanonicalBasis
    {rowGroups : Slice Std.U8} {groupValues : Slice RawQM31}
    {alpha1 alpha2 : RawQM31}
    {foldedGroups : alloc.vec.Vec Std.U8}
    {foldedValues : alloc.vec.Vec RawQM31}
    (source : GroupedRowsTwiceSourceTrace rowGroups groupValues alpha1 alpha2
      foldedGroups foldedValues) : Type where
  b0 : CanonicalRaw
  b1 : CanonicalRaw
  b2 : CanonicalRaw
  b3 : CanonicalRaw
  b4 : CanonicalRaw
  b5 : CanonicalRaw
  b6 : CanonicalRaw
  b7 : CanonicalRaw
  b8 : CanonicalRaw
  b9 : CanonicalRaw
  b10 : CanonicalRaw
  b11 : CanonicalRaw
  b12 : CanonicalRaw
  b13 : CanonicalRaw
  b14 : CanonicalRaw
  b15 : CanonicalRaw
  basisExact : source.basis = basis16 b0.raw b1.raw b2.raw b3.raw b4.raw
    b5.raw b6.raw b7.raw b8.raw b9.raw b10.raw b11.raw b12.raw b13.raw
    b14.raw b15.raw
  b0Exact : exact b0 = 1
  b1Exact : exact b1 = generatedQm31ToExact alpha1 ^ 3
  b2Exact : exact b2 = generatedQm31ToExact alpha1 ^ 2
  b3Exact : exact b3 = generatedQm31ToExact alpha1
  b4Exact : exact b4 = generatedQm31ToExact alpha2 ^ 3
  b5Exact : exact b5 = generatedQm31ToExact alpha2 ^ 3 * generatedQm31ToExact alpha1 ^ 3
  b6Exact : exact b6 = generatedQm31ToExact alpha2 ^ 3 * generatedQm31ToExact alpha1 ^ 2
  b7Exact : exact b7 = generatedQm31ToExact alpha2 ^ 3 * generatedQm31ToExact alpha1
  b8Exact : exact b8 = generatedQm31ToExact alpha2 ^ 2
  b9Exact : exact b9 = generatedQm31ToExact alpha2 ^ 2 * generatedQm31ToExact alpha1 ^ 3
  b10Exact : exact b10 = generatedQm31ToExact alpha2 ^ 2 * generatedQm31ToExact alpha1 ^ 2
  b11Exact : exact b11 = generatedQm31ToExact alpha2 ^ 2 * generatedQm31ToExact alpha1
  b12Exact : exact b12 = generatedQm31ToExact alpha2
  b13Exact : exact b13 = generatedQm31ToExact alpha2 * generatedQm31ToExact alpha1 ^ 3
  b14Exact : exact b14 = generatedQm31ToExact alpha2 * generatedQm31ToExact alpha1 ^ 2
  b15Exact : exact b15 = generatedQm31ToExact alpha2 * generatedQm31ToExact alpha1

theorem source_basis_is_canonical_tensor
    {rowGroups : Slice Std.U8} {groupValues : Slice RawQM31}
    {alpha1 alpha2 : RawQM31}
    {foldedGroups : alloc.vec.Vec Std.U8}
    {foldedValues : alloc.vec.Vec RawQM31}
    (source : GroupedRowsTwiceSourceTrace rowGroups groupValues alpha1 alpha2
      foldedGroups foldedValues)
    (alpha1Canonical : GeneratedCanonicalQM31 alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2) :
    Nonempty (CanonicalBasis source) := by
  obtain ⟨alpha1SquaredExpected, alpha1SquareRun,
      alpha1SquaredCanonical, alpha1SquaredExact⟩ :=
    generated_qm31_square_corresponds alpha1 alpha1Canonical
  have alpha1SquaredEq : source.alpha1Squared = alpha1SquaredExpected :=
    Result.ok.inj (source.alpha1SquareRun.symm.trans alpha1SquareRun)
  subst alpha1SquaredExpected
  obtain ⟨alpha2SquaredExpected, alpha2SquareRun,
      alpha2SquaredCanonical, alpha2SquaredExact⟩ :=
    generated_qm31_square_corresponds alpha2 alpha2Canonical
  have alpha2SquaredEq : source.alpha2Squared = alpha2SquaredExpected :=
    Result.ok.inj (source.alpha2SquareRun.symm.trans alpha2SquareRun)
  subst alpha2SquaredExpected
  obtain ⟨alpha1CubedExpected, alpha1CubeRun,
      alpha1CubedCanonical, alpha1CubeExact⟩ :=
    generated_qm31_mul_corresponds source.alpha1Squared alpha1
      alpha1SquaredCanonical alpha1Canonical
  have alpha1CubedEq : source.alpha1Cubed = alpha1CubedExpected :=
    Result.ok.inj (source.alpha1CubeRun.symm.trans alpha1CubeRun)
  subst alpha1CubedExpected
  have alpha1CubedExact : generatedQm31ToExact source.alpha1Cubed =
      generatedQm31ToExact alpha1 ^ 3 := by
    rw [alpha1CubeExact, alpha1SquaredExact]
    ring
  obtain ⟨alpha2CubedExpected, alpha2CubeRun,
      alpha2CubedCanonical, alpha2CubeExact⟩ :=
    generated_qm31_mul_corresponds source.alpha2Squared alpha2
      alpha2SquaredCanonical alpha2Canonical
  have alpha2CubedEq : source.alpha2Cubed = alpha2CubedExpected :=
    Result.ok.inj (source.alpha2CubeRun.symm.trans alpha2CubeRun)
  subst alpha2CubedExpected
  have alpha2CubedExact : generatedQm31ToExact source.alpha2Cubed =
      generatedQm31ToExact alpha2 ^ 3 := by
    rw [alpha2CubeExact, alpha2SquaredExact]
    ring
  obtain ⟨basisTrace⟩ := generated_basis_exposes_tensor_entries
    alpha1 alpha2 source.alpha1Squared source.alpha2Squared
    source.alpha1Cubed source.alpha2Cubed source.basis alpha1Canonical
    alpha2Canonical alpha1SquaredCanonical alpha2SquaredCanonical
    alpha1CubedCanonical alpha2CubedCanonical source.basisRun
  let b0 : CanonicalRaw := one
  let b1 : CanonicalRaw := ⟨source.alpha1Cubed, alpha1CubedCanonical⟩
  let b2 : CanonicalRaw := ⟨source.alpha1Squared, alpha1SquaredCanonical⟩
  let b3 : CanonicalRaw := ⟨alpha1, alpha1Canonical⟩
  let b4 : CanonicalRaw := ⟨source.alpha2Cubed, alpha2CubedCanonical⟩
  let b5 : CanonicalRaw := mul b4 b1
  let b6 : CanonicalRaw := mul b4 b2
  let b7 : CanonicalRaw := mul b4 b3
  let b8 : CanonicalRaw := ⟨source.alpha2Squared, alpha2SquaredCanonical⟩
  let b9 : CanonicalRaw := mul b8 b1
  let b10 : CanonicalRaw := mul b8 b2
  let b11 : CanonicalRaw := mul b8 b3
  let b12 : CanonicalRaw := ⟨alpha2, alpha2Canonical⟩
  let b13 : CanonicalRaw := mul b12 b1
  let b14 : CanonicalRaw := mul b12 b2
  let b15 : CanonicalRaw := mul b12 b3
  have b5Raw : b5.raw = basisTrace.b5 := Result.ok.inj
    ((mul_run b4 b1).symm.trans basisTrace.b5Run)
  have b6Raw : b6.raw = basisTrace.b6 := Result.ok.inj
    ((mul_run b4 b2).symm.trans basisTrace.b6Run)
  have b7Raw : b7.raw = basisTrace.b7 := Result.ok.inj
    ((mul_run b4 b3).symm.trans basisTrace.b7Run)
  have b9Raw : b9.raw = basisTrace.b9 := Result.ok.inj
    ((mul_run b8 b1).symm.trans basisTrace.b9Run)
  have b10Raw : b10.raw = basisTrace.b10 := Result.ok.inj
    ((mul_run b8 b2).symm.trans basisTrace.b10Run)
  have b11Raw : b11.raw = basisTrace.b11 := Result.ok.inj
    ((mul_run b8 b3).symm.trans basisTrace.b11Run)
  have b13Raw : b13.raw = basisTrace.b13 := Result.ok.inj
    ((mul_run b12 b1).symm.trans basisTrace.b13Run)
  have b14Raw : b14.raw = basisTrace.b14 := Result.ok.inj
    ((mul_run b12 b2).symm.trans basisTrace.b14Run)
  have b15Raw : b15.raw = basisTrace.b15 := Result.ok.inj
    ((mul_run b12 b3).symm.trans basisTrace.b15Run)
  exact ⟨{
    b0 := b0, b1 := b1, b2 := b2, b3 := b3
    b4 := b4, b5 := b5, b6 := b6, b7 := b7
    b8 := b8, b9 := b9, b10 := b10, b11 := b11
    b12 := b12, b13 := b13, b14 := b14, b15 := b15
    basisExact := by
      rw [basisTrace.outputExact]
      apply Subtype.ext
      simp only [basis16, b0, one, b1, b2, b3, b4, b5, b6, b7, b8, b9,
        b10, b11, b12, b13, b14, b15, b5Raw, b6Raw, b7Raw, b9Raw,
        b10Raw, b11Raw, b13Raw, b14Raw, b15Raw]
    b0Exact := exact_one
    b1Exact := alpha1CubedExact
    b2Exact := alpha1SquaredExact
    b3Exact := rfl
    b4Exact := alpha2CubedExact
    b5Exact := by
      rw [mul_exact]
      change generatedQm31ToExact source.alpha2Cubed *
        generatedQm31ToExact source.alpha1Cubed = _
      rw [alpha2CubedExact, alpha1CubedExact]
    b6Exact := by
      rw [mul_exact]
      change generatedQm31ToExact source.alpha2Cubed *
        generatedQm31ToExact source.alpha1Squared = _
      rw [alpha2CubedExact, alpha1SquaredExact]
    b7Exact := by
      rw [mul_exact]
      change generatedQm31ToExact source.alpha2Cubed *
        generatedQm31ToExact alpha1 = _
      rw [alpha2CubedExact]
    b8Exact := alpha2SquaredExact
    b9Exact := by
      rw [mul_exact]
      change generatedQm31ToExact source.alpha2Squared *
        generatedQm31ToExact source.alpha1Cubed = _
      rw [alpha2SquaredExact, alpha1CubedExact]
    b10Exact := by
      rw [mul_exact]
      change generatedQm31ToExact source.alpha2Squared *
        generatedQm31ToExact source.alpha1Squared = _
      rw [alpha2SquaredExact, alpha1SquaredExact]
    b11Exact := by
      rw [mul_exact]
      change generatedQm31ToExact source.alpha2Squared *
        generatedQm31ToExact alpha1 = _
      rw [alpha2SquaredExact]
    b12Exact := rfl
    b13Exact := by
      rw [mul_exact]
      change generatedQm31ToExact alpha2 *
        generatedQm31ToExact source.alpha1Cubed = _
      rw [alpha1CubedExact]
    b14Exact := by
      rw [mul_exact]
      change generatedQm31ToExact alpha2 *
        generatedQm31ToExact source.alpha1Squared = _
      rw [alpha1SquaredExact]
    b15Exact := by
      rw [mul_exact]
      rfl }⟩

#print axioms source_basis_is_canonical_tensor

end V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalBasis
