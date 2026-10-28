import PV_B3P_RustResult
namespace PV_B3P_HelperPlan224
open Aeneas Aeneas.Std PV_B3P_RustResult
set_option autoImplicit false

def run {F E : Type} (eval : Nat → Result (core.result.Result F E)) (r : Nat) :
    Nat → List F → Result (core.result.Result (List F) E)
  | 0,out => .ok (.Ok out)
  | n+1,out => bindR (eval r) (fun value => run eval (r+1) n (out.set r value))

theorem append {F E : Type} (eval : Nat → Result (core.result.Result F E))
    (r m n : Nat) (out : List F) :
    run eval r (m+n) out = bindR (run eval r m out) (fun middle => run eval (r+m) n middle) := by
  induction m generalizing r out with
  | zero => simp [run,bindR]
  | succ m ih =>
    rw [Nat.succ_add,run,run,bindR_assoc]
    congr 1
    funext value
    rw [ih]
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

#print axioms append
end PV_B3P_HelperPlan224
