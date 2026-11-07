import NMX_R2_InputInjection
set_option autoImplicit false
namespace NMX_R2_ArgsInjection
open Aeneas Aeneas.Std NMX_R2_Carrier NMX_R2_ScalarCarrier
/-- No native input is silently identified with another canonical argument. -/
theorem injective : Function.Injective NMX_R2_CallArguments.auth := by
 intro a b same
 cases a with
 | mk ap aa app al ast =>
   cases b with
   | mk bp ba bpp bl bst =>
     have hp := NMX_R2_KeyCarrier.key_injective (congrArg RSL.TX2_233.Args.verifier_program same)
     have hpool := NMX_R2_KeyCarrier.key_injective (congrArg RSL.TX2_233.Args.pool_program same)
     have hl := byte_injective (congrArg RSL.TX2_233.Args.output_lane same)
     have hs := long_injective (congrArg RSL.TX2_233.Args.current_slot same)
     have haccts : aa = ba := by
      apply Subtype.ext
      exact (List.map_inj_right (fun x y h => NMX_R2_InputInjection.account h)).mp
       (congrArg RSL.TX2_233.Args.accounts same)
     cases hp; cases hpool; cases hl; cases hs; cases haccts
     rfl
#print axioms injective
end NMX_R2_ArgsInjection
