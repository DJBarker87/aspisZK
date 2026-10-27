import FJg_HighSum
import FJg_PartialSum
import FJg_LiteralTensor
import FJg_OriginalDigitValues
import FJd_HighReference
import FJg_TensorProduct
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_HighReference
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv

/-- Source high4/partial16 contraction uses the SAME literal constructor point,
SAME common16 values and SAME parsed final-message coefficients. -/
theorem value (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FJg_LiteralTensor.source semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (f : Slice U8) (common : Array NQ 16#usize) (partials : Array NE 4#usize)
    (vcom : ∀ j,j<16 → FJf_QMArray.value common j=FJf_CommonCell.model (FJg_LiteralTensor.source semAlpha) j)
    (vp : FJg_PartialsValue.Values f common partials 4)
    (row : Array (Array NQ 4#usize) 5#usize) (coeff : Array NQ 4#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok row)
    (hd : Array.index_usize row 4#usize=ok coeff) :
    FJg_HighCell.sumPrefix partials coeff 4=
      ∑ i : Fin 64,FJc_InactiveCoefficientsModel.field f i.val*
        FJg_TensorProduct.high (FJg_LiteralTensor.factors semAlpha) i := by
  let g := FJg_LiteralTensor.factors semAlpha
  let commonModel : Fin 16 → OraclePortCheckpointAbiC5.E := fun j=>
    g 2 ⟨j.val%4,Nat.mod_lt _ (by decide)⟩*g 3 ⟨j.val/4%4,Nat.mod_lt _ (by decide)⟩
  have shared : FJg_HighCell.sumPrefix partials coeff 4=
      FJd_HighReference.shared (fun i=>FJc_InactiveCoefficientsModel.field f i.val) commonModel (g 4) := by
    rw [FJg_HighSum.four]
    unfold FJd_HighReference.shared
    apply Finset.sum_congr rfl
    intro s _
    rw [FJg_PartialSum.value f common partials vp s,
      FJg_OriginalDigitValues.value semAlpha z w hc hw 4#usize (by decide) row coeff hr hd s]
    change (∑ j : Fin 16, _)*g 4 s=_
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [vcom j.val j.isLt,FJf_CommonCell.model,map_mul]
    rfl
  rw [shared,FJd_HighReference.value]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  dsimp only [commonModel,FJg_TensorProduct.high]
  have e0 : i.val%16%4=i.val%4 := by omega
  have e1 : i.val%16/4%4=i.val/4%4 := by omega
  rw [e0,e1]
#print axioms value
end AspisR1.FJg_HighReference
end
