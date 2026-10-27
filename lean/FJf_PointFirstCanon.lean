import FJf_PointLoop
import FJf_PointOuterFrame
import FJf_RawPointOuterFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PointFirstCanon
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
open FJc_WeightQMBridge (SQ)
open FJf_FactorArray (value)

theorem value (points : Points) (p : Array SQ 10#usize)
    (hp : Array.index_usize points 0#usize=ok p) (hc : FJc_WeightArray.canonical p)
    (factors out : Factors) (hf : FJf_FactorArray.canon factors)
    (run : FIn_WeightsExtract.weights_new_loop0 {start:=0#usize,«end»:=3#usize}
      points factors=ok out) :
    ∀ row,out.val[0]?=some row → FJf_FactorArray.rowCanon row := by
  rw [FIn_WeightsExtract.weights_new_loop0,loop] at run
  cases hb : FIn_WeightsExtract.weights_new_loop0.body points
      {start:=0#usize,«end»:=3#usize} factors with
  | fail e => simp only [hb] at run;cases run
  | div => simp only [hb] at run;cases run
  | ok r =>
    simp only [hb] at run
    cases r with
    | done f =>
      have no := FJf_PointOuterBody.done points _ factors f hb
      have bad : (3:Nat)≤0 := no.1
      omega
    | cont next =>
      rcases next with ⟨cursor,mid⟩
      obtain ⟨k,hn,hm⟩ := FJf_PointOuterBody.cont points _ cursor factors mid hb
      have pr := FIo_RangeNext.some_next _ cursor k hn
      have hk : k=0#usize := pr.1
      subst k
      have first := FJf_PointLoop.five points 0#usize p hp hc factors mid hf hm
      have tail : FIn_WeightsExtract.weights_new_loop0 cursor points mid=ok out := run
      have fr := FJf_RawPointOuterFrame.loop points 0 cursor mid out (by have := pr.2.2.1;change 0 < cursor.start.val;omega) tail
      intro row hr
      rw [fr] at hr
      exact first.1 row (List.mem_of_getElem? hr)
#print axioms value
end AspisR1.FJf_PointFirstCanon
end
