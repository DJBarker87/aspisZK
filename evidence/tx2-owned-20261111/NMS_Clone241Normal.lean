import NMS_Clone242Normal
import NMS_CloneRef241
set_option autoImplicit false
namespace NMS_Clone241Normal
open RSL RSL.TX2_241 NMS_NormalRefine
/-- Normal observation equality at arbitraryV: the corrected clone reference
adds only stopped getter arms, not new normal values, errors or event traces. -/
theorem normal (L : PoolLib) (D : DeployedIds) (V : V2Lib)
 (child : ∀ a, Normal (NMS_CloneRef242.Ref L D a) (TX2_242.Ref L D a))
 (a : Args) : Normal (NMS_CloneRef241.Ref L D V a) (Ref L D V a) := by
 unfold NMS_CloneRef241.Ref Ref
 apply NMS_NormalCalls.seq (refl _)
 apply rsbind (NMS_NormalCalls.call _ _ _ child _)
 intro validated
 apply rsbind (refl _)
 intro account0
 apply rsbind (NMS_CloneNormal.normal account0.bytes)
 intro proof
 apply rsbind (refl _)
 intro account6
 apply rsbind (NMS_CloneNormal.normal account6.bytes)
 intro checkpoint
 exact refl _
#print axioms normal
end NMS_Clone241Normal
