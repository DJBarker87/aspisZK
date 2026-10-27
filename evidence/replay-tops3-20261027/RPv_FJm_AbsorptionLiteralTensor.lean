import RPv_FJm_AbsorptionScale
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionLiteralTensor
open Aeneas Aeneas.Std
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (alpha : Array K 10#usize) (j : Fin 1024) :
    FJd_PointReference.tensor (fun d s=>algebraMap FK FE (FJm_AbsorptionScale.factors alpha d s)) j=
      algebraMap FK FE (tensorPoint
        (R0P.SemSource.xor12Point (FJf_ModelPoint.decoded
          (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))) j) := by
  rw [←FJd_PointReference.original (R0P.SemSource.xor12Point
    (FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))) j]
  unfold FJd_PointReference.tensor FJm_AbsorptionScale.factors
  rw [map_prod]
#print axioms value
end AspisR1.FJm_AbsorptionLiteralTensor
end
