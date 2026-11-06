import NLK_BorrowScope
set_option autoImplicit false
namespace NLK_ProgramBorrowScope
open Aeneas Aeneas.Std Result NLF_ParentModel NLF_SdkModel
abbrev PE := AdapterRw.solana_program_error.ProgramError
structure Outcome (A : Type) where
 parent : Parent
 result : Result (core.result.Result A PE)
/-- The SDK's singleton acquisition error and the child's full ProgramError
are DIFFERENT carriers. A returned child Err is a value inside the guard scope,
and therefore still performs Drop. Reuse the proved SDK bracket, no new guard. -/
def liftChild {A : Type} (child : Payload → Result (core.result.Result A PE))
    (bytes : Payload) : Result (Except ProgramError (core.result.Result A PE)) :=
 match child bytes with
 | .ok reply => .ok (.ok reply)
 | .fail e => .fail e
 | .div => .div

def project {A : Type} (r : NLK_BorrowScope.Outcome (core.result.Result A PE)) : Outcome A :=
 ⟨r.parent,match r.result with
  | .ok (.ok reply) => .ok reply
  | .ok (.error _) => .ok (.Err .AccountBorrowFailed)
  | .fail e => .fail e
  | .div => .div⟩

def run {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (core.result.Result A PE)) : Outcome A :=
 project (NLK_BorrowScope.run p account (liftChild child))

theorem invariant {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (core.result.Result A PE)) (valid : Invariant p) :
    Invariant (run p account child).parent :=
 NLK_BorrowScope.invariant p account (liftChild child) valid

theorem acquire_error {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (core.result.Result A PE)) (e : ProgramError)
    (cut : (acquire p account .shared).2 = .error e) :
    run p account child =
      ⟨(acquire p account .shared).1,.ok (.Err .AccountBorrowFailed)⟩ := by
 unfold run
 rw [NLK_BorrowScope.acquire_error p account (liftChild child) e cut]
 rfl

theorem child_abort {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (core.result.Result A PE))
    (guard : NLF_RefCell.Guard) (bytes : Payload) (e : Error)
    (acq : (acquire p account .shared).2 = .ok guard)
    (read : (NLF_ParentModel.deref (acquire p account .shared).1 guard).2 = .ok bytes)
    (abort : child bytes = .fail e) :
    run p account child =
      ⟨(NLF_ParentModel.deref (acquire p account .shared).1 guard).1,.fail e⟩ := by
 unfold run
 rw [NLK_BorrowScope.child_abort p account (liftChild child) guard bytes e acq read
   (by simp only [liftChild,abort])]
 rfl

theorem child_returned {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (core.result.Result A PE))
    (guard : NLF_RefCell.Guard) (bytes : Payload) (reply : core.result.Result A PE)
    (acq : (acquire p account .shared).2 = .ok guard)
    (read : (NLF_ParentModel.deref (acquire p account .shared).1 guard).2 = .ok bytes)
    (returned : child bytes = .ok reply)
    (dropped : (NLF_ParentModel.release
      (NLF_ParentModel.deref (acquire p account .shared).1 guard).1 guard).2 = .ok ()) :
    run p account child =
      ⟨(NLF_ParentModel.release
        (NLF_ParentModel.deref (acquire p account .shared).1 guard).1 guard).1,.ok reply⟩ := by
 unfold run
 rw [NLK_BorrowScope.child_returned p account (liftChild child) guard bytes (.ok reply)
   acq read (by simp only [liftChild,returned]) dropped]
 rfl

#print invariant
#print axioms invariant
#print axioms acquire_error
#print axioms child_abort
#print child_returned
#print axioms child_returned
end NLK_ProgramBorrowScope
