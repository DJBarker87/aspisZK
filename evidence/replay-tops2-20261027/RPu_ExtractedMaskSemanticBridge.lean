import R0P.MaskValue
import RPu_ExtractedMaskPopulatedMeaning
import RPu_ExtractedMaskLinearMap

/-! Explicit field-hom transport from the actual selected-mask caller's local
exact-tower formula to the existing `R0P.Mask.maskValue` formula. The theorem
retains canonical source-input premises and exposes basis compatibility as a
genuine assumption. It does not instantiate the hom for WideExact and does not
identify the source and semantic carriers. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskSemanticBridge

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev C1 := AspisR1.ExtractedMaskCoefficientStep.C1
abbrev MaskOnly := AspisR1.ExtractedMaskCoefficientStep.MaskOnly
abbrev CanonicalQM := AspisR1.ExtractedMaskCallerModel.CanonicalQM
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

private def mappedC1Cell {K : Type} [Field K]
    (f : ExactQM →+* K) (c1 : C1) (j : Fin 16) : K :=
  f (decode (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))

private def mappedMaskCell {K : Type} [Field K]
    (f : ExactQM →+* K) (maskOnly : MaskOnly) (j : Fin 10) : K :=
  f (decode (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j))

private def mappedPoint {K : Type} [Field K]
    (f : ExactQM →+* K) (point : Array QM 10#usize) : Fin 10 → K :=
  fun i => f (AspisR1.ExtractedMaskLinearsExact.decodedPoint point i)

private def basisIndex16 (j : Fin 16) : Fin 4 :=
  ⟨j.val % 4, Nat.mod_lt _ (by omega)⟩

private def basisIndex10 (j : Fin 10) : Fin 4 :=
  ⟨j.val % 4, Nat.mod_lt _ (by omega)⟩

private theorem factorExponent_eq_local (j : Fin 16) :
    R0P.Mask.factorExponent j =
      AspisR1.ExtractedMaskCoefficientArray.c1Exponent j := by
  apply Fin.ext
  fin_cases j <;>
    norm_num [R0P.Mask.factorExponent,
      AspisR1.ExtractedMaskCoefficientArray.c1Exponent]

private theorem maskExponent_eq_local (j : Fin 10) :
    R0P.Mask.maskOnlyFactorExponent j =
      AspisR1.ExtractedMaskCoefficientArray.maskExponent j := by
  apply Fin.ext
  fin_cases j <;>
    norm_num [R0P.Mask.maskOnlyFactorExponent,
      AspisR1.ExtractedMaskCoefficientArray.maskExponent]

private theorem local_maskLinear_eq_old {K : Type} [Field K]
    (family : Nat) (alpha : Fin 10 → K) :
    AspisR1.ExtractedMaskLinearRecurrence.maskLinear family alpha =
      R0P.Mask.maskLinear family alpha := rfl

private theorem map_scheduled_polynomial
    {K : Type} [Field K] {F : Subfield K}
    (B : R0P.PackBasis F) (f : ExactQM →+* K)
    (basisCompatible : ∀ j : Fin 4,
      f (AspisR1.ExtractedMaskTowerBasisExact.basisElement j.val) =
        R0P.Mask.towerBasis B j)
    (c1 : C1) (maskOnly : MaskOnly) (point : Array QM 10#usize)
    (x0 : ExactQM)
    (hlinear0 : f x0 = R0P.Mask.maskLinear 0 (mappedPoint f point)) :
    f (AspisR1.ExtractedMaskPopulatedMeaning.scheduledPolynomial
        c1 maskOnly x0) =
      (∑ j : Fin 16,
        (R0P.Mask.maskFactors B (mappedPoint f point)).c1 j *
          mappedC1Cell f c1 j) +
      ∑ j : Fin 10,
        (R0P.Mask.maskFactors B (mappedPoint f point)).maskOnly j *
          mappedMaskCell f maskOnly j := by
  unfold AspisR1.ExtractedMaskPopulatedMeaning.scheduledPolynomial
  rw [map_add, map_sum, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    change f (AspisR1.ExtractedMaskCoefficientLoopMeaning.c1Meaning c1 j *
        x0 ^ (AspisR1.ExtractedMaskCoefficientArray.c1Exponent j).val) = _
    unfold AspisR1.ExtractedMaskCoefficientLoopMeaning.c1Meaning mappedC1Cell
    unfold R0P.Mask.maskFactors R0P.Mask.mulTowerBasis
    have hbasis : f (AspisR1.ExtractedMaskTowerBasisExact.basisElement (j.val % 4)) =
        R0P.Mask.towerBasis B (basisIndex16 j) := by
      simpa [basisIndex16] using basisCompatible (basisIndex16 j)
    dsimp only [R0P.Mask.maskFactors]
    rw [map_mul, map_mul, map_pow, hlinear0, hbasis, factorExponent_eq_local j]
    have hidx : basisIndex16 j = ⟨j.val % 4, Nat.mod_lt _ (by omega)⟩ := by
      apply Fin.ext
      rfl
    rw [hidx]
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    change f (AspisR1.ExtractedMaskCoefficientLoopMeaning.maskMeaning maskOnly j *
        x0 ^ (AspisR1.ExtractedMaskCoefficientArray.maskExponent j).val) = _
    unfold AspisR1.ExtractedMaskCoefficientLoopMeaning.maskMeaning mappedMaskCell
    unfold R0P.Mask.maskFactors R0P.Mask.mulTowerBasis
    have hbasis : f (AspisR1.ExtractedMaskTowerBasisExact.basisElement (j.val % 4)) =
        R0P.Mask.towerBasis B (basisIndex10 j) := by
      simpa [basisIndex10] using basisCompatible (basisIndex10 j)
    dsimp only [R0P.Mask.maskFactors]
    rw [map_mul, map_mul, map_pow, hlinear0, hbasis, maskExponent_eq_local j]
    have hidx : basisIndex10 j = ⟨j.val % 4, Nat.mod_lt _ (by omega)⟩ := by
      apply Fin.ext
      rfl
    rw [hidx]
    ring

private theorem map_explicit_term
    {K : Type} [Field K] {F : Subfield K}
    (B : R0P.PackBasis F) (f : ExactQM →+* K)
    (point : Array QM 10#usize) (g : QM) (x16 : ExactQM)
    (hlinear16 : f x16 = R0P.Mask.maskLinear 16 (mappedPoint f point)) :
    f ((1 + x16 ^ 26) * decode g) =
      (R0P.Mask.maskFactors B (mappedPoint f point)).explicitG * f (decode g) := by
  rw [map_mul, map_add, map_one, map_pow, hlinear16]
  rfl

private theorem map_local_mask_formula
    {K : Type} [Field K] {F : Subfield K}
    (B : R0P.PackBasis F) (f : ExactQM →+* K)
    (basisCompatible : ∀ j : Fin 4,
      f (AspisR1.ExtractedMaskTowerBasisExact.basisElement j.val) =
        R0P.Mask.towerBasis B j)
    (c1 : C1) (maskOnly : MaskOnly) (g : QM)
    (point : Array QM 10#usize)
    (hlinear0 : f (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
        (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) =
      R0P.Mask.maskLinear 0 (mappedPoint f point))
    (hlinear16 : f (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
        (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) =
      R0P.Mask.maskLinear 16 (mappedPoint f point)) :
    f (AspisR1.ExtractedMaskPopulatedMeaning.scheduledPolynomial c1 maskOnly
        (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
          (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) +
        (1 + (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
          (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) ^ 26) * decode g) =
      R0P.Mask.maskValue B (mappedC1Cell f c1) (mappedMaskCell f maskOnly)
        (f (decode g)) (mappedPoint f point) := by
  calc
    _ = f (AspisR1.ExtractedMaskPopulatedMeaning.scheduledPolynomial c1 maskOnly
          (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
            (AspisR1.ExtractedMaskLinearsExact.decodedPoint point))) +
        f ((1 + (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
          (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) ^ 26) * decode g) := by
          rw [map_add]
    _ = (∑ j : Fin 16,
          (R0P.Mask.maskFactors B (mappedPoint f point)).c1 j *
            mappedC1Cell f c1 j) +
        (∑ j : Fin 10,
          (R0P.Mask.maskFactors B (mappedPoint f point)).maskOnly j *
            mappedMaskCell f maskOnly j) +
        (R0P.Mask.maskFactors B (mappedPoint f point)).explicitG * f (decode g) := by
          rw [map_scheduled_polynomial B f basisCompatible c1 maskOnly point _ hlinear0,
            map_explicit_term B f point g _ hlinear16]
    _ = R0P.Mask.maskValue B (mappedC1Cell f c1) (mappedMaskCell f maskOnly)
        (f (decode g)) (mappedPoint f point) := by
          unfold R0P.Mask.maskValue
          ring

/-- The actual extracted selected-mask computation transports to the prior
`R0P.Mask.maskValue` model under an explicit field hom and basis compatibility.
The concrete hom and compatibility for `WideExact` are intentionally not
instantiated here. -/
theorem current_selected_mask_maps_to_maskValue
    {K : Type} [Field K] {F : Subfield K}
    (B : R0P.PackBasis F) (f : ExactQM →+* K)
    (basisCompatible : ∀ j : Fin 4,
      f (AspisR1.ExtractedMaskTowerBasisExact.basisElement j.val) =
        R0P.Mask.towerBasis B j)
    (c1 : C1) (maskOnly : MaskOnly) (g : QM)
    (point : Array QM 10#usize)
    (hc1 : ∀ j : Fin 16, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))
    (hmask : ∀ j : Fin 10, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j))
    (hpoint : ∀ i : Nat, ∀ hi : i < 10, CanonicalQM
      (AspisR1.ExtractedMaskLinearLoop.pointAtNat point i hi))
    (hg : CanonicalQM g) :
    ∃ out : QM,
      state_only_hiding.state_only_selected_mask_value c1 maskOnly g point = .ok out ∧
      CanonicalQM out ∧
      f (decode out) =
        R0P.Mask.maskValue B (mappedC1Cell f c1) (mappedMaskCell f maskOnly)
          (f (decode g)) (mappedPoint f point) := by
  have hlinear0 : f (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
      (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) =
      R0P.Mask.maskLinear 0 (mappedPoint f point) := by
    calc
      f (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
          (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) =
          AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
            (fun i => f (AspisR1.ExtractedMaskLinearsExact.decodedPoint point i)) :=
            AspisR1.ExtractedMaskLinearMap.map_maskLinear f 0
              (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)
      _ = R0P.Mask.maskLinear 0 (mappedPoint f point) := rfl
  have hlinear16 : f (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
      (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) =
      R0P.Mask.maskLinear 16 (mappedPoint f point) := by
    calc
      f (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
          (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) =
          AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
            (fun i => f (AspisR1.ExtractedMaskLinearsExact.decodedPoint point i)) :=
            AspisR1.ExtractedMaskLinearMap.map_maskLinear f 16
              (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)
      _ = R0P.Mask.maskLinear 16 (mappedPoint f point) := rfl
  obtain ⟨out, hrun, houtCanonical, hvalue⟩ :=
    AspisR1.ExtractedMaskPopulatedMeaning.current_selected_mask_value_scheduled
      c1 maskOnly g point hc1 hmask hpoint hg
  refine ⟨out, hrun, houtCanonical, ?_⟩
  calc
    f (decode out) = f (
        AspisR1.ExtractedMaskPopulatedMeaning.scheduledPolynomial c1 maskOnly
          (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
            (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) +
        (1 + (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
          (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) ^ 26) * decode g) :=
      congrArg f hvalue
    _ = R0P.Mask.maskValue B (mappedC1Cell f c1) (mappedMaskCell f maskOnly)
        (f (decode g)) (mappedPoint f point) :=
      map_local_mask_formula B f basisCompatible c1 maskOnly g point hlinear0 hlinear16

#print axioms current_selected_mask_maps_to_maskValue

end AspisR1.ExtractedMaskSemanticBridge
