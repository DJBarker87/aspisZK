import ExtractedMaskSemanticBridge
import R1ConcretePackBasis
import ExtractedMaskTowerBasisExact
import R0P.MaskValue

/-! Concrete instantiation of the selected-mask hom/basis interface for the
retained exact `WideExact` carrier.  This only supplies the algebraic map and
the four basis equations; it does not add a source-refinement claim. -/

set_option autoImplicit false
namespace AspisR1.ExtractedMaskSemanticBridgeConcrete

open Aeneas Aeneas.Std
open AspisV8R15.ExactTowerBase

abbrev K := AspisWideTower.WideExact
abbrev F := AspisR1.ExactBaseProjection.embed.fieldRange
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev B := R0P.PackBasis F

def qm31ToWide : ExactQM →+* K := algebraMap ExactQM K

noncomputable def packBasis : B := AspisR1.ConcretePackBasis.basis

private theorem map_iQM :
    qm31ToWide AspisR1.ExtractedMaskTowerBasisExact.iQM =
      AspisR1.ConcretePackBasis.iE := by
  rfl

private theorem map_uQM :
    qm31ToWide AspisR1.ExtractedMaskTowerBasisExact.uQM =
      AspisR1.ConcretePackBasis.uE := by
  rfl

private theorem packBasis_i : packBasis.i = AspisR1.ConcretePackBasis.iE := by
  rfl

private theorem packBasis_u : packBasis.u = AspisR1.ConcretePackBasis.uE := by
  rfl

/-- The four literal exact-tower basis elements agree with the existing
`ConcretePackBasis` elements after the `QM31Exact → WideExact` algebra map. -/
theorem basisCompatible : ∀ j : Fin 4,
    qm31ToWide (AspisR1.ExtractedMaskTowerBasisExact.basisElement j.val) =
      R0P.Mask.towerBasis packBasis j := by
  intro j
  fin_cases j
  · change qm31ToWide 1 = 1
    simp [qm31ToWide]
  · change qm31ToWide AspisR1.ExtractedMaskTowerBasisExact.iQM = packBasis.i
    rw [map_iQM, packBasis_i]
  · change qm31ToWide AspisR1.ExtractedMaskTowerBasisExact.uQM = packBasis.u
    rw [map_uQM, packBasis_u]
  · change qm31ToWide
      (AspisR1.ExtractedMaskTowerBasisExact.iQM *
        AspisR1.ExtractedMaskTowerBasisExact.uQM) =
      packBasis.i * packBasis.u
    rw [map_mul, map_iQM, map_uQM, packBasis_i, packBasis_u]

#print axioms basisCompatible

private abbrev QM := AspisR1.ExtractedMaskSemanticBridge.QM
private abbrev C1 := AspisR1.ExtractedMaskSemanticBridge.C1
private abbrev MaskOnly := AspisR1.ExtractedMaskSemanticBridge.MaskOnly
private abbrev CanonicalQM := AspisR1.ExtractedMaskSemanticBridge.CanonicalQM
private abbrev decode := AspisR1.ExtractedMaskSemanticBridge.decode

private def mappedC1Cell (c1 : C1) (j : Fin 16) : K :=
  qm31ToWide (decode (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))

private def mappedMaskCell (maskOnly : MaskOnly) (j : Fin 10) : K :=
  qm31ToWide (decode (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j))

private def mappedPoint (point : Array QM 10#usize) : Fin 10 → K :=
  fun i => qm31ToWide
    (AspisR1.ExtractedMaskLinearsExact.decodedPoint point i)

/-- Apply the generic explicit-hom bridge using the already-proved concrete
packing basis. -/
theorem current_selected_mask_maps_to_maskValue
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
      AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
        c1 maskOnly g point = .ok out ∧
      CanonicalQM out ∧
      qm31ToWide (decode out) =
        R0P.Mask.maskValue packBasis (mappedC1Cell c1) (mappedMaskCell maskOnly)
          (qm31ToWide (decode g)) (mappedPoint point) := by
  exact AspisR1.ExtractedMaskSemanticBridge.current_selected_mask_maps_to_maskValue
    packBasis qm31ToWide basisCompatible c1 maskOnly g point hc1 hmask hpoint hg

#print axioms current_selected_mask_maps_to_maskValue

end AspisR1.ExtractedMaskSemanticBridgeConcrete
