import RPv_FJj_LowSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_ScaleModel
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)
attribute [local irreducible] QuadraticAlgebra.instInv FJg_DualTensor.low

theorem value (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FJg_LiteralTensor.source semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (d : Fin 5) (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok row)
    (hd : Array.index_usize row (Usize.ofNat d.val (by have := d.isLt;scalar_tac))=ok digit)
    (a : NE) (p : Array NE 4#usize) (ha : FIo_WideValues.Canon a)
    (hp : FIo_Native.weights.powers 4#usize a=ok p) :
    decodeM FIo_Native.weights.QUARTER • FJg_ScalarCell.sumPrefix p digit 4=
      FJg_DualTensor.low (FJg_LiteralTensor.factors semAlpha d) (decodeWide (wide a)) := by
  rw [FJg_ScaleSum.value semAlpha z w hc hw d row digit hr hd a p ha hp]
  exact FJj_LowSum.value _ _
#print axioms value
end AspisR1.FJj_ScaleModel
end
