import Aeneas
set_option autoImplicit false
namespace AspisR1.JGo_TX2_LoopChain
open Aeneas Aeneas.Std Result ControlFlow

theorem source {S R : Type} (body : S → Result (ControlFlow S R))
    (s : Nat → S) (n : Nat) (out : R)
    (steps : ∀ i,i<n → body (s i)=ok (.cont (s (i+1))))
    (last : body (s n)=ok (.done out)) : loop body (s 0)=ok out := by
  induction n generalizing s with
  | zero => rw [loop.eq_def,last]
  | succ n ih =>
    rw [loop.eq_def,steps 0 (by omega)]
    exact ih (fun i=>s (i+1)) (fun i hi=>steps (i+1) (by omega)) last
#print axioms source
end AspisR1.JGo_TX2_LoopChain
