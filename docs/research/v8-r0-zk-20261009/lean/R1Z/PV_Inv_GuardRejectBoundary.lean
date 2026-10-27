import R1Z.PV_Inv_PreGuard
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardRejectBoundary
open R0P R0Z.HonestValidity
variable {K : Type} [Field K] [DecidableEq K]

theorem rejects_iff (t : Trace K) (lambda chi : K) :
    PV_Inv_PreGuard.noPoleRef t lambda chi = false ↔ ¬ NoPole t lambda chi := by
  rw [←PV_Inv_PreGuard.source_equation]
  exact Bool.eq_false_iff

/-- The P guard cannot be inferred from rejection. It is a distinct logical
condition, needed for the actual poleBad membership. -/
theorem guarded_reject (t : Trace K) (lambda chi : K) (P : Prop) :
    (P ∧ PV_Inv_PreGuard.noPoleRef t lambda chi = false) ↔ P ∧ ¬ NoPole t lambda chi := by
  rw [rejects_iff]

#print axioms rejects_iff
#print axioms guarded_reject
end R1Z.PV_Inv_GuardRejectBoundary
