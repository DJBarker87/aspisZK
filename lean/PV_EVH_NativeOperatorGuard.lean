import PV_EVH_NativeOperators
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeOperatorGuard
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62

theorem guard_view (base : ExternalTypes) (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (v : transport.Variant) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    PV_EVH_Prefix.FinishedView (PV_EVH_VariantGuard.guard v)
      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v .S2) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  cases v with
  | S1 => exact PV_EVH_Prefix.lift_fixed (.ok true)
  | S2 => exact PV_EVH_Prefix.lift_fixed (.ok false)
  | D => exact PV_EVH_Prefix.lift_fixed (.ok true)
#print axioms guard_view
end PV_EVH_NativeOperatorGuard
