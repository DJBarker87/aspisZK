import FJg_SharedProvenance
import FJg_SharedHighCall
import FJg_PartialsValue
import FJg_OriginalDigitCanon
import FJg_HighValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_Part1High
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)
/-- High contraction VALUE on the actual installed Pair's own shared operands. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8) (kappa out : AspisR1Stage2.Stage2Finish.E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (common : Array NQ 16#usize) (partials : Array NE 4#usize)
      (row : Array (Array NQ 4#usize) 5#usize) (coeff : Array NQ 4#usize) (high : NE),
      FJf_QMArray.canon common ∧
      (∀ j,j<16 → FJf_QMArray.value common j=
        FJf_CommonCell.model (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) j) ∧
      FIo_Native.weights.shared_partials f common=ok (.Ok partials) ∧
      FJg_PartialsValue.Values f common partials 4 ∧
      Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok row ∧
      Array.index_usize row 4#usize=ok coeff ∧
      FIo_Native.weights.high_dot partials coeff=ok (.Ok high) ∧
      FIo_WideValues.Canon high ∧ decodeWide (wide high)=FJg_HighCell.sumPrefix partials coeff 4 := by
  obtain ⟨ap0,ap1,common,partials,before,after,hg,hcom,vcom,hpart,hhigh⟩ :=
    FJg_SharedProvenance.value r semAlpha z w alpha f kappa out hc hw folds run
  have pv := FJg_PartialsValue.four f common hcom partials hpart
  obtain ⟨row,coeff,high,hr,hd,hh⟩ := FJg_SharedHighCall.reached _ partials ap0 ap1 before after hhigh
  have cq := FJg_OriginalDigitCanon.value semAlpha z w hc hw 4#usize row coeff hr hd
  have hv := FJg_HighValue.four partials coeff pv.1 cq high hh
  exact ⟨common,partials,row,coeff,high,hcom,vcom,hpart,pv.2,hr,hd,hh,hv⟩
#print axioms value
end AspisR1.FJg_Part1High
end
