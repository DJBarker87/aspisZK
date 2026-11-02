import PV_EVH_NativeRawHistoryError
import PV_EVH_LinuxRawSpatial
import PV_EVH_LinuxRawThreaded
import PV_EVH_LinuxRawHistoryTrace
import PV_EVH_NativeEntropyMemory
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeRawReceipt
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (State Cleared)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (buffer initial run)
open PV_EVH_NativeRawSelection (rawBase atWorld)

/-- Connected native error branch plus continuous private memory receipts,
complete ordered driver events and preservation of old live stack bytes.
Original frame admission and actual kernel/ABI association remain P; this
is not full-entry or L3 adequacy and provides no actual success witness. -/
theorem error_receipts (base : ExternalTypes)
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
      ((PV_EVH_Runtime.sourceProjection r.outcome = some
        (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
          mask limit retry) ∧
      Cleared slot r.state ∧ PV_EVH_LinuxRawCodes.ValidCode e ∧
      PV_EVH_StackAdmission.HeapCoherent r.state ∧
      r.state.frame.live = w.frame.live ∧
      r.events = history.delivery.events ++ PV_EVH_StackZero.emitted slot) ∧
      (∀ c ∈ history.calls, ∀ i, i < c.length →
        (∀ b ∈ w.frame.runtime.heap, ∀ j, j < b.bytes.length → c.address+i ≠ b.address+j) ∧
        (∀ old ∈ w.frame.live, ∀ j, j < old.initialized → c.address+i ≠ old.address+j)) ) ∧
      PV_EVH_LinuxRawThreaded.Threaded initial wi.frame.runtime.base history.calls
        history.delivery.buffer history.delivery.world ∧
      r.events = history.calls.flatMap (fun c => c.after.events) ++
        PV_EVH_StackZero.emitted slot ∧
      (∀ old ∈ w.frame.live, ∀ i, i < old.initialized →
        r.state.memory (old.address+i) = w.memory (old.address+i)) := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry owner address kernel fuel success w e
  dsimp only
  intro hr hs hl hc he
  have h := PV_EVH_NativeRawSpatial.error_with_request_frames base heap box ops
    mask limit retry owner address kernel fuel success w e hr hs hl hc he
  refine ⟨h, PV_EVH_LinuxRawThreaded.continuous
    (PV_EVH_LinuxRawObserve.call kernel) address fuel 0 initial _, ?_, ?_⟩
  · rw [PV_EVH_LinuxRawHistoryTrace.events_exact]
    exact h.1.2.2.2.2.2
  · let slot := PV_EVH_EntropySourceSlot.original owner address w
    let driver := PV_EVH_LinuxRawControl.driver (fun code => code)
      (PV_EVH_LinuxRawObserve.call kernel) address fuel
    let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
    let d := driver buffer wi
    have hd := PV_EVH_NativeRawHistoryError.driver_status base kernel address fuel wi e he
    exact PV_EVH_NativeEntropyMemory.error_live_memory (rawBase base) heap box
      (atWorld ops d) mask limit retry slot driver success w e hr rfl hl hd

#print axioms error_receipts
end PV_EVH_NativeRawReceipt
