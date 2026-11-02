import PV_EVH_NativeEntropyIteration
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyIterationError
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (Slot State Cleared)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (initial buffer restore run)

/-- Complete source-iteration error result at the native wrapper selection,
original slot admission, partial-fill physical cleanup, allocator/errno frame,
retired memory and every emitted event. This is an error-branch theorem; the
actual driver, stack-frame provenance and successful continuation stay P. -/
theorem error_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (slot : Slot)
      (driver : Slice U8 → State → PV_EVH_StackEntropyFill.Delivery)
      (success : (Slice U8 → zeroize.Zeroizing (Array U8 64#usize)) → Slice U8 → Q Answer)
      (w : State) (e : getrandom.error.Error), retry < limit → slot.initialized = 64 →
      let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
      let d := driver buffer wi
      d.status = .returned (.ok (.Err e)) →
      getrandom.fill buffer = .ok (.Err e,(Array.to_slice_mut d.buffer).1) →
      let r := run mask limit retry slot driver success w
      PV_EVH_Runtime.sourceProjection r.outcome = some
        (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
          mask limit retry) ∧
      Cleared slot r.state ∧ r.state.frame.runtime = d.runtime ∧
      r.state.frame.retired = slot :: w.frame.retired ∧
      r.state.history = w.history ++
        (PV_EVH_ZeroizeArray.events slot.key 0 slot.initialized).map
          (PV_EVH_ZeroAddressBridge.physical slot.address) ∧
      r.events = d.events ++ PV_EVH_StackZero.emitted slot := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry slot driver success w e hr hn hd hf
  let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
  let d := driver buffer wi
  have hout : (PV_EVH_StackEntropyFill.fill slot driver buffer wi).outcome =
      .returned (.ok (.Err e,(Array.to_slice_mut d.buffer).1)) := by
    simp only [PV_EVH_StackEntropyFill.fill,PV_EVH_StackEntropyFill.reply,hd]
  have hlookup := PV_EVH_StackEntropyFill.admitted_lookup slot
    (PV_EVH_StackEntropyFill.encode initial) driver buffer w
  dsimp only
  rw [PV_EVH_NativeEntropyIteration.run_step base heap box ops mask limit retry
    slot driver success w hr]
  rw [PV_EVH_NativeEntropyError.error_world slot.key
    (PV_EVH_StackEntropyFill.fill slot driver buffer) (success restore) wi e
    (Array.to_slice_mut d.buffer).1 slot hout hlookup hn]
  rw [PV_EVH_NativeEntropyIteration.source_error base heap box ops mask limit retry e
    (Array.to_slice_mut d.buffer).1 hr hf]
  exact ⟨rfl,PV_EVH_StackZero.dropped_cleared slot _,
    PV_EVH_StackZero.dropped_runtime slot _,PV_EVH_StackZero.retired_after_drop slot _,
    PV_EVH_StackZero.dropped_history slot _,rfl⟩

#print axioms error_native
end PV_EVH_NativeEntropyIterationError
