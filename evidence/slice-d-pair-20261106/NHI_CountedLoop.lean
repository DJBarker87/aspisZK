import NHE_LoopMap
set_option autoImplicit false
namespace NHI_CountedLoop
open Aeneas Aeneas.Std Result ControlFlow

/-- Finite interpreter of the exact one-step Result, including abort prefixes. -/
def unroll {S A : Type} (body : S → Result (ControlFlow S A)) : Nat → S → Result A
 | 0,_ => div
 | fuel+1,s => do
  let cf ← body s
  match cf with
  | .done a => ok a
  | .cont next => unroll body fuel next

theorem agrees {S A : Type} (body : S → Result (ControlFlow S A)) (rank : S → Nat)
 (decreases : ∀ s next,body s=ok (.cont next) → rank next<rank s)
 (fuel : Nat) (s : S) (enough : rank s<fuel) : loop body s=unroll body fuel s := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
  rw [loop.eq_def]
  simp only [unroll]
  cases run : body s with
  | fail e => rfl
  | div => rfl
  | ok cf =>
   cases cf with
   | done a => rfl
   | cont next =>
    exact ih next (by have h:=decreases s next run;omega)

#print axioms agrees
end NHI_CountedLoop
