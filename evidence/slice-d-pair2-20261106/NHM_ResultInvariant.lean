import NHI_CountedLoop
set_option autoImplicit false
namespace NHM_ResultInvariant
open Aeneas Aeneas.Std Result ControlFlow

theorem terminal {S A : Type} (body : S→Result (ControlFlow S A)) (P : A→Prop)
 (law : ∀ s a,body s=ok (.done a)→P a)
 (fuel : Nat) (s : S) (a : A) (run : NHI_CountedLoop.unroll body fuel s=ok a) : P a := by
 induction fuel generalizing s with
 | zero=>cases run
 | succ fuel ih=>
  simp only [NHI_CountedLoop.unroll] at run
  cases step : body s with
  | fail e=>simp only [step] at run;cases run
  | div=>simp only [step] at run;cases run
  | ok cf=>
   simp only [step,bind_tc_ok] at run
   cases cf with
   | done value=>cases Result.ok.inj run;exact law s a step
   | cont next=>exact ih next run

/-- Simultaneously propagate arbitrary state invariants and the actual terminal
Result property; rejected prefixes are kept, never assumed away. -/
theorem stateful {S A : Type} (body : S→Result (ControlFlow S A))
 (P : S→Prop) (Q : A→Prop)
 (preserve : ∀ s t,P s→body s=ok (.cont t)→P t)
 (finish : ∀ s a,P s→body s=ok (.done a)→Q a)
 (fuel : Nat) (s : S) (a : A) (initial : P s)
 (run : NHI_CountedLoop.unroll body fuel s=ok a) : Q a := by
 induction fuel generalizing s with
 | zero=>cases run
 | succ fuel ih=>
  simp only [NHI_CountedLoop.unroll] at run
  cases step : body s with
  | fail e=>simp only [step] at run;cases run
  | div=>simp only [step] at run;cases run
  | ok cf=>
   simp only [step,bind_tc_ok] at run
   cases cf with
   | done value=>cases Result.ok.inj run;exact finish s a initial step
   | cont next=>exact ih next (preserve s next initial step) run

#print axioms terminal
#print axioms stateful
end NHM_ResultInvariant
