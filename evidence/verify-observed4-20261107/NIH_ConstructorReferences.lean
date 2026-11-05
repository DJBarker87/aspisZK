import NIH_CopyLift
import NIH_RawSource
import NDE_LiftBridge
import NDE_RawBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_ConstructorReferences
/-- Safe-reference extraction carrier transport for the actual copy lift. -/
theorem lift (value : U32) :
 NDE_LiftBridge.mapResult NDE_LiftBridge.toNative (NDE_Reference.lift_ref value)=
 FIq_Native.pool_v1.pair_forest_copy_terminal.lift_m31 value :=
 NDE_LiftBridge.copy_lift value
/-- Safe-reference extraction carrier transport for every raw four-word input. -/
theorem raw (limbs : Array U64 4#usize) :
 NDE_LiftBridge.mapResult NDE_RawBridge.toNative (NDE_Reference2.extension_raw_ref limbs)=
 FIq_Native.state_only_poseidon.extension_from_raw_limbs limbs :=
 NDE_RawBridge.extension_raw limbs
#print axioms lift
#print axioms raw
end AspisR1.NIH_ConstructorReferences
