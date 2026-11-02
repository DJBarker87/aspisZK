import PV_EVH_NativeEntropyIterationError
import PV_EVH_LinuxRawObserve
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeRawSelection
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_NativeEntropyIteration (buffer)

/-- Per-reached-call source dictionary. It is computed from that world's native
primitive delivery, never from a whole-helper answer or final trace. Other slice
inputs retain the residual dictionary. Faults/exhaustion have no source view.
This is not a uniform FinishedView across advancing entropy worlds. -/
def atWorld [ExternalTypes] (ops : ExternalFuns)
    (d : PV_EVH_StackEntropyFill.Delivery) : ExternalFuns := by
  classical
  exact {ops with op129 := fun s =>
    if s = buffer then
      match PV_EVH_StackEntropyFill.reply d with
      | .returned r => r
      | _ => ops.op129 s
    else ops.op129 s}

/-- The source wrapper's error carrier is fixed to its underlying integer;
all_codes proves every reached code is nonzero and representable by i32.
Representation and machine-code preservation remain explicitly V370. -/
def rawBase (base : ExternalTypes) : ExternalTypes := {base with op7 := Int}

theorem error_carrier (base : ExternalTypes) :
    @getrandom.error.Error (types (rawBase base)) = Int := rfl

/-- Exact op129 installation at opsNative for the currently reached call. -/
theorem error_fill (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    ∀ (d : PV_EVH_StackEntropyFill.Delivery) (e : getrandom.error.Error),
      d.status = .returned (.ok (.Err e)) →
      letI : ExternalFuns := opsNative base heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      getrandom.fill buffer = .ok (.Err e,(Array.to_slice_mut d.buffer).1) := by
  letI : ExternalTypes := types base
  intro d e hd
  change (atWorld ops d).op129 buffer = _
  simp only [atWorld,if_pos rfl,PV_EVH_StackEntropyFill.reply,hd]

#print axioms error_carrier
#print axioms error_fill
end PV_EVH_NativeRawSelection
