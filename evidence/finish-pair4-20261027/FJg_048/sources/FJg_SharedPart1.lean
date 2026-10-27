import FJg_SharedHighTrace
import FJg_HighValue
import FJg_ScalarValue
import FJg_OriginalDigitCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_SharedPart1
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)

theorem value (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (partials ap0 ap1 : Array NE 4#usize)
    (hp : FIo_ArrayCanon.Holds partials) (cp0 : FIo_ArrayCanon.Holds ap0) (cp1 : FIo_ArrayCanon.Holds ap1)
    (before after : Array NE 7#usize)
    (run : FIo_Native.weights.shared_high partials (FIo_Install.toWeights w) ap0 ap1 before=ok (.Ok (),after)) :
    ∃ (row : Array (Array NQ 4#usize) 5#usize) (coeff low0 low1 : Array NQ 4#usize),
      Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok row ∧
      Array.index_usize row 4#usize=ok coeff ∧
      Array.index_usize row 0#usize=ok low0 ∧ Array.index_usize row 1#usize=ok low1 ∧
      FIp_ArrayValue.value after 1=
        (decodeM FIo_Native.weights.QUARTER • FJg_ScalarCell.sumPrefix ap0 low0 4)*
        (decodeM FIo_Native.weights.QUARTER • FJg_ScalarCell.sumPrefix ap1 low1 4)*
        FJg_HighCell.sumPrefix partials coeff 4 := by
  obtain ⟨row,coeff,low0,low1,high,s0,s1,scale,val,old,absorption,back,
    hr,h4,hh,h0,hs0,h1,hs1,hm,hv,hb,hu⟩ := FJg_SharedHighTrace.reached _ partials ap0 ap1 before after run
  have cc := FJg_OriginalDigitCanon.value semAlpha z w hc hw 4#usize row coeff hr h4
  have vh := FJg_HighValue.four partials coeff hp cc high hh
  have vs0 := FJg_ScalarValue.value ap0 low0 cp0 s0 hs0
  have vs1 := FJg_ScalarValue.value ap1 low1 cp1 s1 hs1
  have vm := FIo_WideMulValues.mul s0 s1 scale vs0.1 vs1.1 hm
  have vv := FIo_WideMulValues.mul scale high val vm.1 vh.1 hv
  refine ⟨row,coeff,low0,low1,hr,h4,h0,h1,?_⟩
  rw [FJg_SharedHighTrace.written before after val old absorption back hb hu,
    vv.2,vm.2,vs0.2,vs1.2,vh.2]
#print axioms value
end AspisR1.FJg_SharedPart1
end
