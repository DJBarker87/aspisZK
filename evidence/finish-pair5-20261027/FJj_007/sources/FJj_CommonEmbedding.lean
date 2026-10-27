import FJj_HighInstances
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_CommonEmbedding
open Aeneas Aeneas.Std
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (semAlpha : Array K 10#usize) (j : Fin 16) :
    algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
      (FJf_CommonCell.model (FJg_LiteralTensor.source semAlpha) j.val)=
        FJj_HighInstances.common (FJg_LiteralTensor.factors semAlpha) j := by
  unfold FJf_CommonCell.model FJj_HighInstances.common FJg_LiteralTensor.factors
  exact map_mul _ _ _
#print axioms value
end AspisR1.FJj_CommonEmbedding
end
