import ExtractedMaskQmPackBase4Arithmetic
import ExtractedMaskSemanticBridgeConcrete

/-! Transport of the exact mathematical four-QM31 packing formula into the
existing concrete `WideExact`/`R0P.pack4` model. This is algebraic plumbing,
not a source refinement result. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4Semantic

noncomputable section

open AspisV8R15.ExactTowerBase

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Wide := AspisWideTower.WideExact
abbrev PackB := AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide

theorem map_mathPack (v : Fin 4 → CurrentQM) :
    f (AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack v) =
      R0P.pack4 PackB (fun j =>
        f (AspisR1.ExtractedMaskQM31Exact.decode (v j))) := by
  have hi : f AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis = PackB.i := by
    have hbase : AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis =
        AspisR1.ExtractedMaskTowerBasisExact.basisElement 1 := rfl
    rw [hbase]
    have h := AspisR1.ExtractedMaskSemanticBridgeConcrete.basisCompatible
      (1 : Fin 4)
    change f (AspisR1.ExtractedMaskTowerBasisExact.basisElement 1) =
      R0P.Mask.towerBasis PackB 1 at h
    simpa [R0P.Mask.towerBasis,
      AspisR1.ExtractedMaskTowerBasisExact.basisElement] using h
  have hu : f AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis = PackB.u := by
    have hbase : AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis =
        AspisR1.ExtractedMaskTowerBasisExact.basisElement 2 := rfl
    rw [hbase]
    have h := AspisR1.ExtractedMaskSemanticBridgeConcrete.basisCompatible
      (2 : Fin 4)
    change f (AspisR1.ExtractedMaskTowerBasisExact.basisElement 2) =
      R0P.Mask.towerBasis PackB 2 at h
    simpa [R0P.Mask.towerBasis,
      AspisR1.ExtractedMaskTowerBasisExact.basisElement] using h
  have hiu : f (AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis *
      AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis) = PackB.i * PackB.u := by
    rw [map_mul, hi, hu]
  simp only [AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack,
    map_add, map_mul, hi, hu, hiu, R0P.pack4]

#print axioms map_mathPack

end
end AspisR1.ExtractedMaskQmPackBase4Semantic
