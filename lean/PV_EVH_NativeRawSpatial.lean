import PV_EVH_NativeRawHistoryError
import PV_EVH_LinuxRawSpatial
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeRawSpatial
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (State Cleared)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (buffer initial run)
open PV_EVH_NativeRawSelection (rawBase atWorld)

/-- Actual extracted error branch, deployed zeroize1.9.0, and every issued
raw request's separation from heap and old live stack owners. This removes
per-request spatial obligations; original frame admission remains explicit P.
No invented address, kernel contract, success witness or trust field. -/
theorem error_with_request_frames (base : ExternalTypes)
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
      (PV_EVH_Runtime.sourceProjection r.outcome = some
        (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
          mask limit retry) ∧
      Cleared slot r.state ∧ PV_EVH_LinuxRawCodes.ValidCode e ∧
      PV_EVH_StackAdmission.HeapCoherent r.state ∧
      r.state.frame.live = w.frame.live ∧
      r.events = history.delivery.events ++ PV_EVH_StackZero.emitted slot) ∧
      (∀ c ∈ history.calls, ∀ i, i < c.length →
        (∀ b ∈ w.frame.runtime.heap, ∀ j, j < b.bytes.length → c.address+i ≠ b.address+j) ∧
        (∀ old ∈ w.frame.live, ∀ j, j < old.initialized → c.address+i ≠ old.address+j)) := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry owner address kernel fuel success w e
  dsimp only
  intro hr hs hl hc he
  have h := PV_EVH_NativeRawHistoryError.error_from_history base heap box ops
    mask limit retry owner address kernel fuel success w e hr hs hl hc he
  refine ⟨h, ?_⟩
  intro c hm i hi
  exact PV_EVH_LinuxRawSpatial.request_separation (PV_EVH_LinuxRawObserve.call kernel)
    owner address fuel initial w hs hl c hm i hi

#print axioms error_with_request_frames
end PV_EVH_NativeRawSpatial
