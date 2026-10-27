import FJj_HighInstances
import FJm_AbsorptionScale
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionHighSource
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
      FJj_HighInstances.shared (fun i=>FJc_InactiveCoefficientsModel.field f i.val)
        (fun j=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
          (FJf_CommonCell.model (FJg_LiteralTensor.source semAlpha) j.val))
        ((fun d s=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJm_AbsorptionScale.factors semAlpha d s)) 4) := by
  rw [FJg_HighSum.four]
  unfold FJj_HighInstances.shared
  apply Finset.sum_congr rfl
  intro s _
  have digitValue := (FJm_AbsorptionDigit.value semAlpha z w hc hw 4#usize (by decide) row coeff hr hd).2 s
  change FJf_QMArray.value coeff s.val=FJm_AbsorptionScale.factors semAlpha ⟨(4#usize).val,by decide⟩ s at digitValue
  have four : (⟨(4#usize).val,by decide⟩ : Fin 5)=4 := by decide
  rw [four] at digitValue
  rw [FJg_PartialSum.value f common partials vp s,digitValue]
  apply congrArg (fun x=>x*(fun d s=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJm_AbsorptionScale.factors semAlpha d s)) 4 s)
  apply Finset.sum_congr rfl
  intro j _
  rw [vcom j.val j.isLt]
#print axioms value
end AspisR1.FJm_AbsorptionHighSource
end
