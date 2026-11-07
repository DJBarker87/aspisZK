import NMS_CloneNormal
import NMS_NormalCalls
import NMS_CloneRef242
set_option autoImplicit false
namespace NMS_Clone242Normal
open RSL NMS_NormalRefine
/-- BOTH normal Ok/Err observations are unchanged by the explicit clone
interpretation, provided the recursively corrected child has this property.
This theorem deliberately gives no canonical credit to added abort arms. -/
theorem normal (L : PoolLib) (D : DeployedIds)
 (child : ∀ a, Normal (NMS_CloneRef233.Ref L D a) (TX2_233.Ref L D a))
 (a : TX2_242.Args) : Normal (NMS_CloneRef242.Ref L D a) (TX2_242.Ref L D a) := by
 unfold NMS_CloneRef242.Ref TX2_242.Ref
 apply NMS_NormalCalls.seq (refl _)
 apply rsbind (refl _)
 intro q
 apply NMS_NormalCalls.seq (refl _)
 apply rsbind (refl _)
 intro lane
 apply rsbind (refl _)
 intro slot
 apply rsbind (NMS_NormalCalls.call _ _ _ child _)
 intro auth
 apply rsbind (refl _)
 intro account
 apply rsbind (NMS_CloneNormal.normal account.bytes)
 intro bytes
 exact refl _
#print axioms normal
end NMS_Clone242Normal
