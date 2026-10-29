import R1Z.PV_RunJoin_NativeActual62
import R1Z.PV_RunJoin_NativeFrames62
import R1Z.PV_RunJoin_Open13262
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeObstruction62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62

def rejecting (base : ExternalTypes) (ops : @ExternalFuns (types base)) : @ExternalFuns (types base) :=
  {ops with op132 := .div}

/-- All CLOSED bindings, including V265, are retained. The OPEN V228 callback
alone obstructs successful capture. This is not a model witness. -/
theorem no_capture (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (rejecting base ops)
    ∀ p, ¬ PV_RunJoin_ActualProvenance60.Produced p := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (rejecting base ops)
  apply PV_RunJoin_Open13262.no_capture
  change @ExternalFuns.op132 (types base) (opsNative base heap box (rejecting base ops)) = .div
  rw [PV_RunJoin_NativeFrames62.op132]
  rfl

theorem not_uniform_capture (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    ¬ (∀ remaining : @ExternalFuns (types base),
      PV_RunJoin_NativeActual62.SuccessfulCapture base heap box remaining) := by
  intro h
  obtain ⟨p⟩ := h (rejecting base ops)
  exact no_capture base heap box ops p.val p.property

#print axioms rejecting
#print axioms no_capture
#print axioms not_uniform_capture
end R1Z.PV_RunJoin_NativeObstruction62
