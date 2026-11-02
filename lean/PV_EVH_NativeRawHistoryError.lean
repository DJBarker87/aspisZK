import PV_EVH_NativeRawError
import PV_EVH_LinuxRawHistory
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeRawHistoryError
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (State Cleared)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (buffer initial run)
open PV_EVH_NativeRawSelection (rawBase atWorld)

/-- Private raw history determines the very same source-bound driver delivery;
no complete helper answer, success-domain assumption or new public payload. -/
theorem driver_status (base : ExternalTypes)
    (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
    (address fuel : Nat) (w : State) (e : Int)
    (h : (PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
      address fuel 0 (Array.repeat 64#usize 0#u8) w.frame.runtime.base).delivery.status =
      .returned (.ok (.Err e))) :
    letI : ExternalTypes := types (rawBase base)
    (PV_EVH_LinuxRawControl.driver (fun code => code)
      (PV_EVH_LinuxRawObserve.call kernel) address fuel buffer w).status =
      .returned (.ok (.Err e)) := by
  letI : ExternalTypes := types (rawBase base)
  change PV_EVH_LinuxRawControl.status (fun code => code)
    (PV_EVH_LinuxRawControl.loop (PV_EVH_LinuxRawObserve.call kernel) address fuel 0
      (Array.repeat 64#usize 0#u8) w.frame.runtime.base).status = _
  rw [PV_EVH_NativeRawError.status_identity base]
  rw [← PV_EVH_LinuxRawHistory.erases]
  exact h

/-- Connect the private all-prefix control history to the actual extracted
error iteration at opsNative. The remaining spatial and kernel-memory P
obligations are identical to error_connected; history does not discharge L3. -/
theorem error_from_history (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base))) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (owner address : Nat)
      (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
      (fuel : Nat)
      (success : (Slice U8 → zeroize.Zeroizing (Array U8 64#usize)) → Slice U8 → Q Answer)
      (w : State) (e : Int),
      let slot := PV_EVH_EntropySourceSlot.original owner address w
      let driver := PV_EVH_LinuxRawControl.driver (fun code => code)
        (PV_EVH_LinuxRawObserve.call kernel) address fuel
      let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
      let history := PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
        address fuel 0 initial wi.frame.runtime.base
      let d := driver buffer wi
      retry < limit →
      PV_EVH_StackAdmission.HeapSeparate slot w →
      PV_EVH_StackAdmission.LiveSeparate slot w →
      PV_EVH_StackAdmission.HeapCoherent w →
      history.delivery.status = .returned (.ok (.Err e)) →
      letI : ExternalFuns := opsNative (rawBase base) heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      let r := run mask limit retry slot driver success w
      PV_EVH_Runtime.sourceProjection r.outcome = some
        (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
          mask limit retry) ∧
      Cleared slot r.state ∧ PV_EVH_LinuxRawCodes.ValidCode e ∧
      PV_EVH_StackAdmission.HeapCoherent r.state ∧
      r.state.frame.live = w.frame.live ∧
      r.events = history.delivery.events ++ PV_EVH_StackZero.emitted slot := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry owner address kernel fuel success w e
  dsimp only
  intro hr hs hl hc he
  have hd := driver_status base kernel address fuel
    (PV_EVH_StackAdmission.enter (PV_EVH_EntropySourceSlot.original owner address w)
      (PV_EVH_StackEntropyFill.encode initial) w) e he
  have h := PV_EVH_NativeRawError.error_connected base heap box ops
    mask limit retry owner address kernel fuel success w e hr hs hl hc hd
  rw [PV_EVH_LinuxRawHistory.erases]
  exact h

#print axioms driver_status
#print axioms error_from_history
end PV_EVH_NativeRawHistoryError
