import PV_B3P_RustResult
namespace PV_B3P_HelperState224
open Aeneas Aeneas.Std PV_B3P_RustResult
set_option autoImplicit false

def run {S E : Type} (action : Nat → S → Result (core.result.Result S E)) (i : Nat) :
    Nat → S → Result (core.result.Result S E)
  | 0,state => .ok (.Ok state)
  | n+1,state => bindR (action i state) (fun next => run action (i+1) n next)

theorem append {S E : Type} (action : Nat → S → Result (core.result.Result S E))
    (i m n : Nat) (state : S) :
    run action i (m+n) state = bindR (run action i m state) (fun middle => run action (i+m) n middle) := by
  induction m generalizing i state with
  | zero => simp [run,bindR]
  | succ m ih =>
    rw [Nat.succ_add,run,run,bindR_assoc]
    congr 1
    funext next
    rw [ih]
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

#print axioms append
end PV_B3P_HelperState224
