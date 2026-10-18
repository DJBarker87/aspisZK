import PoseidonResidualFieldTransport
import ExtractedMaskSemanticBridgeConcrete
import ExtractedMaskQmPackBase4Arithmetic
import ExtractedMaskTowerBasisExact
import PoseidonExternalPackedModel

set_option autoImplicit false
namespace AspisR1.PoseidonCandidateScalarResidualWide
noncomputable section
open AspisV8R15.ExactTowerBase
open R0P
open AspisR1.PoseidonResidualFieldTransport

abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Wide := AspisWideTower.WideExact
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
abbrev PackB := AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis
abbrev lane := AspisR1.PoseidonExternalPackedModel.lane
abbrev iBasis := AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
abbrev uBasis := AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis

/-- Map the exact-tower scalar-residual packing to the retained concrete
WideExact `R0P.pack4` encoding. The three ordered residual branches stay
inside the generic ring-hom theorem. -/
theorem map_scalar_residual_pack (o : R0P.Openings ExactQM)
    (block : ExactQM) (low : Fin 16 → ExactQM) (group : Fin 4) :
    f (R0P.poseidonPackingFormula iBasis uBasis (fun j =>
      R0P.poseidonScalarResidual o block low (lane group j))) =
    R0P.poseidonPackingFormula PackB.i PackB.u (fun j =>
      R0P.poseidonScalarResidual
        (AspisR1.ValueFamilyFieldTransport.mapOpenings f o) (f block)
        (AspisR1.PoseidonMap.mapState f low) (lane group j)) := by
  have hi : f iBasis = PackB.i := by
    have hbase : iBasis = AspisR1.ExtractedMaskTowerBasisExact.basisElement 1 := rfl
    rw [hbase]
    have h := AspisR1.ExtractedMaskSemanticBridgeConcrete.basisCompatible
      (1 : Fin 4)
    change f (AspisR1.ExtractedMaskTowerBasisExact.basisElement 1) =
      R0P.Mask.towerBasis PackB 1 at h
    simpa [R0P.Mask.towerBasis,
      AspisR1.ExtractedMaskTowerBasisExact.basisElement] using h
  have hu : f uBasis = PackB.u := by
    have hbase : uBasis = AspisR1.ExtractedMaskTowerBasisExact.basisElement 2 := rfl
    rw [hbase]
    have h := AspisR1.ExtractedMaskSemanticBridgeConcrete.basisCompatible
      (2 : Fin 4)
    change f (AspisR1.ExtractedMaskTowerBasisExact.basisElement 2) =
      R0P.Mask.towerBasis PackB 2 at h
    simpa [R0P.Mask.towerBasis,
      AspisR1.ExtractedMaskTowerBasisExact.basisElement] using h
  have hmap := AspisR1.PoseidonResidualFieldTransport.map_packed_scalarResidual
    (f := f) o block iBasis uBasis low
    (fun j : Fin 4 => lane group j)
  rw [hi, hu] at hmap
  exact hmap

#print axioms map_scalar_residual_pack
end
end AspisR1.PoseidonCandidateScalarResidualWide
