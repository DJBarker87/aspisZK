import NHI_CountedLoop
set_option autoImplicit false
namespace NIG_LoopPost
open Aeneas Aeneas.Std Result ControlFlow

/-- A result invariant follows from each SAME native/model step; failure and
nonreturn branches cannot produce a successful output. -/
theorem post {S A : Type} (body : S → Result (ControlFlow S A))
 (P : S → Prop) (Q : A → Prop)
 (keep : ∀ s t, P s → body s=ok (.cont t) → P t)
 (done : ∀ s a, P s → body s=ok (.done a) → Q a)
 (fuel : Nat) (s : S) (a : A) (hs : P s)
 (run : NHI_CountedLoop.unroll body fuel s=ok a) : Q a := by
 induction fuel generalizing s with
 | zero => cases run
 | succ fuel ih =>
  cases step : body s with
  | fail e => simp only [NHI_CountedLoop.unroll,step,bind_tc_fail] at run; cases run
  | div => simp only [NHI_CountedLoop.unroll,step,bind_tc_div] at run; cases run
  | ok cf =>
   cases cf with
   | cont t =>
    simp only [NHI_CountedLoop.unroll,step,bind_tc_ok] at run
    exact ih t (keep s t hs step) run
   | done out =>
    simp only [NHI_CountedLoop.unroll,step,bind_tc_ok] at run
    cases Result.ok.inj run
    exact done s a hs step
#print axioms post
end NIG_LoopPost
