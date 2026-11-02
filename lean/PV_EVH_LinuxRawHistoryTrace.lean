import PV_EVH_LinuxRawHistory
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawHistoryTrace
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawControl (Reply)
open PV_EVH_LinuxRawHistory (execute)
open PV_EVH_World (World)

/-- The ordered private syscall receipts account for every event of the raw
control delivery, even on failure, faults and exhaustion. Private bytes are
never published by this flattening; only each call's existing events are used. -/
theorem events_exact
    (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel offset : Nat) (a : Array U8 64#usize) (w : World) :
    ((execute syscall address fuel offset a w).calls.flatMap
      (fun c => c.after.events)) = (execute syscall address fuel offset a w).delivery.events := by
  induction fuel generalizing offset a w with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute,List.flatMap_cons]
    cases hr : (syscall (address+offset) (64-offset) a w).result with
    | fault e => simp only [hr,List.flatMap_nil,List.append_nil]
    | exhausted => simp only [hr,List.flatMap_nil,List.append_nil]
    | returned r =>
      cases r with
      | fail e => simp only [hr,List.flatMap_nil,List.append_nil]
      | div => simp only [hr,List.flatMap_nil,List.append_nil]
      | ok ret =>
        simp only [hr]
        split_ifs <;> simp only [List.flatMap_nil,List.append_nil,ih]

#print axioms events_exact
end PV_EVH_LinuxRawHistoryTrace
