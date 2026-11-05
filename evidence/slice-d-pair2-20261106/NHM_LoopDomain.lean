import NHI_CountedLoop
set_option autoImplicit false
namespace NHM_LoopDomain
open Aeneas Aeneas.Std Result ControlFlow

/-- Every attempted state, including the state whose next operation rejects. -/
def all {S A : Type} (body : S→Result (ControlFlow S A)) (P : S→Prop) : Nat→S→Prop
 | 0,s=>P s
 | fuel+1,s=>P s ∧ match body s with
   | .ok (.cont next)=>all body P fuel next
   | _=>True

/-- Finite induction exposes the callee domain at every reached call, without
assuming the loop or any child succeeds. -/
theorem invariant {S A : Type} (body : S→Result (ControlFlow S A)) (P : S→Prop)
 (preserves : ∀ s t,P s→body s=ok (.cont t)→P t)
 (fuel : Nat) (s : S) (initial : P s) : all body P fuel s := by
 induction fuel generalizing s with
 | zero=>exact initial
 | succ fuel ih=>
  refine ⟨initial,?_⟩
  cases run : body s with
  | fail e=>trivial
  | div=>trivial
  | ok cf=>
   cases cf with
   | done out=>trivial
   | cont next=>exact ih next (preserves s next initial run)

#print axioms invariant
end NHM_LoopDomain
