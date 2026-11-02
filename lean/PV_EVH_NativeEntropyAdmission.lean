import PV_EVH_NativeEntropyIterationError
import PV_EVH_StackEntropyCoherence
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyAdmission
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (initial buffer restore run)

/-- Native iteration cleanup preserves physical heap coherence and exactly the
previous live owners under the original-frame admission invariant. The actual
driver's heap preservation and frame/address provenance remain named P inputs. -/
theorem error_coherent (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (slot : Slot)
      (driver : Slice U8 → State → PV_EVH_StackEntropyFill.Delivery)
      (success : (Slice U8 → zeroize.Zeroizing (Array U8 64#usize)) → Slice U8 → Q Answer)
      (w : State) (e : getrandom.error.Error), retry < limit →
      PV_EVH_StackEntropyCoherence.Admission slot w →
      PV_EVH_StackAdmission.HeapCoherent w →
      let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
      let d := driver buffer wi
      d.status = .returned (.ok (.Err e)) → d.runtime.heap = w.frame.runtime.heap →
      PV_EVH_StackAdmission.HeapCoherent (run mask limit retry slot driver success w).state ∧
      (run mask limit retry slot driver success w).state.frame.live = w.frame.live := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry slot driver success w e hr ha hc
  dsimp only
  intro hd hh
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
      (PV_EVH_StackEntropyFill.encode initial) driver buffer w) ha.1]
  exact ⟨PV_EVH_StackEntropyCoherence.cleanup_heap slot d _ w hc ha.2.2.1 hh,
    PV_EVH_StackEntropyCoherence.cleanup_live slot d _ w ha.2.1⟩

#print axioms error_coherent
end PV_EVH_NativeEntropyAdmission
