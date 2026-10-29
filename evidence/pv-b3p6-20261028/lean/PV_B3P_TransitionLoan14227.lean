import PV_B3P_ScalarSemanticBinding13227
namespace PV_B3P_Loans14227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227
set_option autoImplicit false
/-- Shared loans retain identity as well as the immutable value; no fresh
allocation, mutable restore, address cast or destructor is introduced. -/
structure Shared14 (α : Type) where
  identity : Nat
  value : α
inductive BorrowedPublic14 (base : ExternalTypes) where
  | Transfer : Shared14 PV_B3P_ScalarBinding13227.PP → Shared14 (PV_B3P_ScalarBinding13227.Late base) → BorrowedPublic14 base
  | Withdrawal : Shared14 PV_B3P_ScalarBinding13227.PW → Shared14 (PV_B3P_ScalarBinding13227.Late base) → BorrowedPublic14 base

def transition_loan14 (base : ExternalTypes) (p : BorrowedPublic14 base) :
    Result (Shared14 (PV_B3P_ScalarBinding13227.Late base)) :=
  match p with
  | .Transfer _ t => .ok t
  | .Withdrawal _ t => .ok t

def erase_public14 (base : ExternalTypes) (p : BorrowedPublic14 base) : Public base :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  match p with
  | .Transfer p t => .Transfer p.value t.value
  | .Withdrawal p t => .Withdrawal p.value t.value

theorem transition_transfer_identity14 (base : ExternalTypes)
    (p : Shared14 PV_B3P_ScalarBinding13227.PP)
    (t : Shared14 (PV_B3P_ScalarBinding13227.Late base)) :
    transition_loan14 base (.Transfer p t) = .ok t := rfl

theorem transition_withdrawal_identity14 (base : ExternalTypes)
    (p : Shared14 PV_B3P_ScalarBinding13227.PW)
    (t : Shared14 (PV_B3P_ScalarBinding13227.Late base)) :
    transition_loan14 base (.Withdrawal p t) = .ok t := rfl

theorem transition_loan_binding14 (base : ExternalTypes) (p : BorrowedPublic14 base) :
    (do let loan ← transition_loan14 base p; .ok loan.value) =
      PV_B3P_ScalarBinding13227.transition_source13 base (erase_public14 base p) := by
  cases p <;> rfl

/-- Complete shared-reference continuation transport. A caller may inspect the
returned loan identity, not merely an independently copied value. -/
theorem transition_loan_continuation14 {β : Type} (base : ExternalTypes)
    (p : BorrowedPublic14 base)
    (next : Shared14 (PV_B3P_ScalarBinding13227.Late base) → Result β) :
    (do let loan ← transition_loan14 base p; next loan) =
      (match p with | .Transfer _ t => next t | .Withdrawal _ t => next t) := by
  cases p <;> rfl
#print axioms transition_transfer_identity14
#print axioms transition_withdrawal_identity14
#print axioms transition_loan_binding14
#print axioms transition_loan_continuation14
end PV_B3P_Loans14227
