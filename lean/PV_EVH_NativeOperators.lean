import PV_EVH_OperatorSource
import PV_EVH_OperatorFrames
import R1Z.PV_RunJoin_NativeFrames62
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeOperators
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62

/-- Selection at runjoin's actual dictionary and allocator requests. This is
an operator source-value law; eventful invocation/drop/heap adequacy remains
an explicit obligation and is not implied by dictionary selection. -/
theorem selection (base : ExternalTypes) (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    PV_EVH_OperatorFrames.Selection (opsNative base heap box ops) := by
  letI : ExternalTypes := types base
  constructor
  · intro T E U F inst r closure
    cases r <;> rfl
  · intro T E F O inst r closure
    rw [R1Z.PV_RunJoin_NativeFrames62.mapErr]
    exact PV_EVH_OperatorSource.mapErr_source inst r closure

theorem variant (base : ExternalTypes) (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (a b : transport.Variant) :
    (opsNative base heap box ops).op233 a b = PV_EVH_VariantGuard.equal a b := by
  cases a <;> cases b <;> rfl

#print axioms selection
#print axioms variant
end PV_EVH_NativeOperators
