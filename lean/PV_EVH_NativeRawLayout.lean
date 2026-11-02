import PV_EVH_NativeRawHistoryError
import PV_EVH_EntropyDeployedLayout
import PV_EVH_NativeRawSpatial
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeRawLayout
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (State Cleared)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (buffer initial run)
open PV_EVH_NativeRawSelection (rawBase atWorld)

/-- Existing error/source/private-history law, using the adopted frame base.
The original slot's heap/live premises are derived from the reached call's
232-byte reservation boundary. FRAME-ENTRY and HEAP-ENTRY remain runtime P;
no heap coherence or kernel write footprint is inferred from assembly. -/
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
      (∀ b ∈ w.frame.runtime.heap, ∀ i, i < b.bytes.length →
        PV_EVH_EntropyDeployedLayout.OutsideFrame address (b.address+i)) →
      (∀ old ∈ w.frame.live, ∀ i, i < old.initialized →
        PV_EVH_EntropyDeployedLayout.OutsideFrame address (old.address+i)) →
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
  have h := PV_EVH_NativeRawSpatial.error_with_request_frames base heap box ops
    mask limit retry owner address kernel fuel success w e hr
    (PV_EVH_EntropyDeployedLayout.heap_frames owner address w hs).1
    (PV_EVH_EntropyDeployedLayout.live_frames owner address w hl).1 hc he
  exact h

#print axioms error_with_request_frames
end PV_EVH_NativeRawLayout
