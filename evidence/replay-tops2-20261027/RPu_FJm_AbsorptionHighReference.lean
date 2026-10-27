import RPu_FJm_AbsorptionHighSource
import RPu_FJm_AbsorptionCommon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionHighReference
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FJg_LiteralTensor.source semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (f : Slice U8) (common : Array NQ 16#usize) (partials : Array NE 4#usize)
    (vcom : ∀ j,j<16 → FJf_QMArray.value common j=FJf_CommonCell.model (FJg_LiteralTensor.source semAlpha) j)
    (vp : FJg_PartialsValue.Values f common partials 4)
    (row : Array (Array NQ 4#usize) 5#usize) (coeff : Array NQ 4#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 2#usize=ok row)
    (hd : Array.index_usize row 4#usize=ok coeff) :
    FJg_HighCell.sumPrefix partials coeff 4=
      ∑ i : Fin 64,FJc_InactiveCoefficientsModel.field f i.val*
        FJg_TensorProduct.high ((fun d s=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJm_AbsorptionScale.factors semAlpha d s))) i := by
  rw [FJm_AbsorptionHighSource.value semAlpha z w hc hw f common partials vcom vp row coeff hr hd]
  have commonEq : (fun j : Fin 16=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
      (FJf_CommonCell.model (FJg_LiteralTensor.source semAlpha) j.val))=
      FJj_HighInstances.common ((fun d s=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJm_AbsorptionScale.factors semAlpha d s))) := by
    funext j
    exact FJm_AbsorptionCommon.value semAlpha j
  rw [commonEq]
  rw [FJj_HighInstances.tower AspisWideTower.wideU 0]
  exact FJj_HighInstances.indices _ _
#print axioms value
end AspisR1.FJm_AbsorptionHighReference
end
