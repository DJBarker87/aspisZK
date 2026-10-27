import FJj_SuccessorBody
import FJj_SuccessorStep
import FJa_ReverseStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorLoop
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)
open FJj_SuccessorStep (decoded)
open FJa_ReverseStep (cursor)

theorem value (z p out : Array SQ 10#usize) (carry : SQ) (e : Usize)
    (bound : e.val≤10) (hz : FJc_WeightArray.canonical z)
    (hp : FJc_WeightArray.canonical p) (hc : Canon carry)
    (run : FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop
      (cursor e) z p carry=ok out) :
    FJc_WeightArray.canonical out ∧ decoded out=
      (FJj_SuccessorModel.eval (decoded z) e.val (decode carry,decoded p)).2 := by
  generalize he : e.val=n
  induction n using Nat.strong_induction_on generalizing p carry e with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      have ez : e=0#usize := by apply UScalar.eq_of_val_eq;change e.val=0;exact he
      subst e
      have hs := FJa_ReverseStep.stop
      unfold FJa_ReverseStep.next at hs
      unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop at run
      rw [loop] at run
      unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body at run
      rw [hs] at run
      simp only [bind_tc_ok] at run
      cases Result.ok.inj run
      exact ⟨hp,rfl⟩
    · obtain ⟨i,hi,hnext⟩ := FJa_ReverseStep.step e (by omega)
      unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop at run
      rw [loop] at run
      cases hb : FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body z (cursor e) p carry with
      | fail err => simp only [hb,bind_tc_fail] at run;cases run
      | div => simp only [hb,bind_tc_div] at run;cases run
      | ok r =>
        have hnext' : FJj_SuccessorCell.next (cursor e)=ok (some i,cursor i) := hnext
        obtain ⟨p1,c1,rfl⟩ := FJj_SuccessorBody.cont z p carry (cursor e) (cursor i) i hnext' r hb
        simp only [hb,bind_tc_ok] at run
        obtain ⟨cp,cc,step⟩ := FJj_SuccessorStep.value z p p1 carry c1 (cursor e) (cursor i) i
          (by omega) hz hp hc hnext' hb
        have tail : FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop
            (cursor i) z p1 c1=ok out := run
        have recur :=  ih i.val (by omega) p1 c1 i (by omega) cp cc tail rfl
        refine ⟨recur.1,?_⟩
        rw [←he,←hi,FJj_SuccessorModel.succ,←step]
        exact recur.2
#print axioms value
end AspisR1.FJj_SuccessorLoop
end
