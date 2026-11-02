import PV_EVH_NativeEntropyAdmission
import PV_EVH_LinuxRawSyscall
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeLinuxEntropy
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (buffer initial run)

/-- Specialize the actual opsNative iteration to deployed linux_raw control.
Driver heap preservation is discharged, including after partial writes and
EINTR prefixes. Admission and actual syscall/error-carrier/dictionary provenance
remain explicit proof obligations, not new trust fields. -/
theorem error_coherent (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (slot : Slot)
      (decode : Int → getrandom.error.Error)
      (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
      (fuel : Nat)
      (success : (Slice U8 → zeroize.Zeroizing (Array U8 64#usize)) → Slice U8 → Q Answer)
      (w : State) (e : getrandom.error.Error), retry < limit →
      PV_EVH_StackEntropyCoherence.Admission slot w →
      PV_EVH_StackAdmission.HeapCoherent w →
      let driver := PV_EVH_LinuxRawControl.driver decode (PV_EVH_LinuxRawSyscall.call kernel) slot.address fuel
      let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
      (driver buffer wi).status = .returned (.ok (.Err e)) →
      PV_EVH_StackAdmission.HeapCoherent (run mask limit retry slot driver success w).state ∧
      (run mask limit retry slot driver success w).state.frame.live = w.frame.live := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry slot decode kernel fuel success w e hr ha hc
  dsimp only
  intro hd
  exact PV_EVH_NativeEntropyAdmission.error_coherent base heap box ops mask limit retry
    slot (PV_EVH_LinuxRawControl.driver decode (PV_EVH_LinuxRawSyscall.call kernel) slot.address fuel) success w e hr ha hc hd
    (PV_EVH_LinuxRawControl.heap_preserved decode (PV_EVH_LinuxRawSyscall.call kernel) slot.address fuel buffer _)

#print axioms error_coherent
end PV_EVH_NativeLinuxEntropy
