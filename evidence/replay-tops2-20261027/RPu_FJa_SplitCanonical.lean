import RPu_FJa_SplitStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SplitCanonical
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)
open FJa_ReverseStep (cursor)
/-- Canonicality across the COMPLETE installed descending parent loop. -/
theorem value {N : Usize} (weights out : Array NQ N) (p : NP) (c : NQ) (e : Usize)
    (hc : Canon c) (hw : canonical weights)
    (hp : field.PreparedQm31Multiplier.new c=ok p)
    (run : FJa_SplitStep.Loop (cursor e) weights p=ok out) : canonical out := by
  generalize he : e.val=n
  induction n using Nat.strong_induction_on generalizing weights e with
  | h n ih =>
    by_cases hz : n=0
    · have ez : e=0#usize := by apply UScalar.eq_of_val_eq; simpa [hz] using he
      subst e
      unfold FJa_SplitStep.Loop at run
      have hs := FJa_ReverseStep.stop
      unfold FJa_ReverseStep.next at hs
      rw [pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0.eq_def, hs] at run
      simp only [bind_tc_ok] at run
      cases Result.ok.inj run
      exact hw
    · obtain ⟨index,hindex,hn⟩ := FJa_ReverseStep.step e (by omega)
      obtain ⟨parent,right,left,i,i1,middle,afterWrite,_,_,_,_,_,_,_,ca,_,tail⟩ :=
        FJa_SplitStep.value weights out p c (cursor e) (cursor index) index hc hw hp hn run
      exact ih index.val (by omega) afterWrite index ca tail rfl
#print axioms value
end AspisR1.FJa_SplitCanonical
end
