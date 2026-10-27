import FJf_PointFirst
set_option autoImplicit false
namespace AspisR1.FJj_PointAdvance
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)

theorem value (points : Points) (iter : FIo_RangeNext.Range) (factors out : Factors)
    (active : iter.start.val < iter.end.val)
    (run : FIn_WeightsExtract.weights_new_loop0 iter points factors=ok out) :
    ∃ (k : Usize) (cursor : FIo_RangeNext.Range) (mid : Factors),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some k,cursor) ∧
      FIn_WeightsExtract.weights_new_loop0_loop0 {start:=0#usize,«end»:=5#usize}
        points factors k=ok mid ∧
      FIn_WeightsExtract.weights_new_loop0 cursor points mid=ok out := by
  rw [FIn_WeightsExtract.weights_new_loop0,loop] at run
  cases hb : FIn_WeightsExtract.weights_new_loop0.body points iter factors with
  | fail err => simp only [hb] at run;cases run
  | div => simp only [hb] at run;cases run
  | ok r =>
    simp only [hb] at run
    cases r with
    | done f =>
      have stop := FJf_PointOuterBody.done points iter factors f hb
      omega
    | cont t =>
      rcases t with ⟨cursor,mid⟩
      obtain ⟨k,hn,hinner⟩ := FJf_PointOuterBody.cont points iter cursor factors mid hb
      exact ⟨k,cursor,mid,hn,hinner,run⟩
#print axioms value
end AspisR1.FJj_PointAdvance
