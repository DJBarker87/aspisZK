import Port2_QueryLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_CallIndex
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port2_QueryLoop
/-- Extract a reached call by its source cursor from the SAME inductive trace. -/
theorem reached (call : LocalCall) (stop : Nat)
    (advance : ∀ a a1 b b1, call a b=ok (.Ok (a1,b1)) → a1.next.val=a.next.val+1)
    (a out : Acc) (b bout : BW) (n : Nat) (trace : Calls call stop a b out bout n)
    (j : Nat) (lower : a.next.val≤j) (upper : j<stop) :
    ∃ a0 a1 b0 b1, a0.next.val=j ∧ call a0 b0=ok (.Ok (a1,b1)) := by
  induction trace with
  | done a b atEnd => omega
  | @step a a1 out b b1 bout n active returned tail ih =>
    by_cases same : a.next.val=j
    · exact ⟨a,a1,b,b1,same,returned⟩
    · exact ih (by have := advance a a1 b b1 returned; omega)
#print axioms reached
end AspisR1.FJl_CallIndex
end
