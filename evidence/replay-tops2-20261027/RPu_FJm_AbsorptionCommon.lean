import RPu_FJm_AbsorptionScale
import RPu_FJj_CommonEmbedding
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionCommon
open Aeneas Aeneas.Std
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
attribute [local irreducible] QuadraticAlgebra.instInv

theorem factor2 {K : Type} [Field K] (p : Fin 10 → K) (s : Fin 4) :
    FJd_PointReference.pointFactors (R0P.SemSource.xor12Point p) 2 s=
      FJd_PointReference.pointFactors p 2 s := rfl

theorem factor3 {K : Type} [Field K] (p : Fin 10 → K) (s : Fin 4) :
    FJd_PointReference.pointFactors (R0P.SemSource.xor12Point p) 3 s=
      FJd_PointReference.pointFactors p 3 s := rfl

theorem value (alpha : Array K 10#usize) (j : Fin 16) :
    algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
      (FJf_CommonCell.model (FJg_LiteralTensor.source alpha) j.val)=
      FJj_HighInstances.common
        (fun d s=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
          (FJm_AbsorptionScale.factors alpha d s)) j := by
  unfold FJf_CommonCell.model FJj_HighInstances.common FJm_AbsorptionScale.factors
  dsimp only []
  rw [factor2,factor3,←map_mul]
  rw [FJf_ModelPoint.factor _ (⟨2,by decide⟩ : Fin 5),FJf_ModelPoint.factor _ (⟨3,by decide⟩ : Fin 5)]
  have e2 : (⟨2,by decide⟩ : Fin 5)=2 := by decide
  have e3 : (⟨3,by decide⟩ : Fin 5)=3 := by decide
  rw [e2,e3]
  simp only [FJg_LiteralTensor.source]
#print axioms factor2
#print axioms factor3
#print axioms value
end AspisR1.FJm_AbsorptionCommon
end
