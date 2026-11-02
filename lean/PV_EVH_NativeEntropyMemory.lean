import PV_EVH_NativeEntropyIterationError
import PV_EVH_StackEntropyFrame
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyMemory
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (initial buffer restore run)

/-- At the installed native wrappers, the original source initializer, partial
fill and deployed zeroize1.9.0 cleanup preserve every other live stack byte.
Original source-frame spatial provenance remains an explicit obligation. -/
theorem error_live_memory (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (slot : Slot)
      (driver : Slice U8 → State → PV_EVH_StackEntropyFill.Delivery)
      (success : (Slice U8 → zeroize.Zeroizing (Array U8 64#usize)) → Slice U8 → Q Answer)
      (w : State) (e : getrandom.error.Error), retry < limit → slot.initialized = 64 →
      PV_EVH_StackAdmission.LiveSeparate slot w →
      let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
      (driver buffer wi).status = .returned (.ok (.Err e)) →
      ∀ old ∈ w.frame.live, ∀ i, i < old.initialized →
      (run mask limit retry slot driver success w).state.memory (old.address+i) =
        w.memory (old.address+i) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry slot driver success w e hr hn hl
  dsimp only
  intro hd old ho i hi
  let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
  let d := driver buffer wi
  have hout : (PV_EVH_StackEntropyFill.fill slot driver buffer wi).outcome =
      .returned (.ok (.Err e,(Array.to_slice_mut d.buffer).1)) := by
    change PV_EVH_StackEntropyFill.reply d = _
    have hstatus : d.status = .returned (.ok (.Err e)) := hd
    simp only [PV_EVH_StackEntropyFill.reply,hstatus]
  rw [PV_EVH_NativeEntropyIteration.run_step base heap box ops mask limit retry
    slot driver success w hr]
  rw [PV_EVH_NativeEntropyError.error_world slot.key
    (PV_EVH_StackEntropyFill.fill slot driver buffer) (success restore) wi e
    (Array.to_slice_mut d.buffer).1 slot hout
    (PV_EVH_StackEntropyFill.admitted_lookup slot
      (PV_EVH_StackEntropyFill.encode initial) driver buffer w) hn]
  exact PV_EVH_StackEntropyFrame.cleanup_live_memory slot old d _ w hl ho i hi

#print axioms error_live_memory
end PV_EVH_NativeEntropyMemory
