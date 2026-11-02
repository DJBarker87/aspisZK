import PV_B3P_PanicPatterns571227
namespace PV_B3P_FixedIndex572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Symbolic fixed-index law: generators emit the slack, rather than reducing
large numerical bounds or assuming a source guard. -/
theorem fixed_guard (index spare : Nat) :
    indexGuard ⟨index, index + spare + 1⟩ := by
  change index < index + spare + 1
  omega

theorem fixed_certificate {α : Type} (index spare : Nat)
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard ⟨index,index + spare + 1⟩) ∧
      branch (indexGuard ⟨index,index + spare + 1⟩) normal first =
        branch (indexGuard ⟨index,index + spare + 1⟩) normal second :=
  (index_out_of_bounds _ normal first second).2 (fixed_guard index spare)
#print axioms fixed_guard
#print axioms fixed_certificate
end PV_B3P_FixedIndex572227
