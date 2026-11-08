import NMX_R8_Children241
import NMX_R8_Factor241
import NMX_R8_Std241
import NMX_R8_VerifierUse241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_EncodedFactor241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def source (s : LIBB_PoolCarriers.Statement) (proof checkpoint : Slice U8)
 (start finish : Usize) (publicBytes : Array U8 1880#usize) :=
 RSL.Spec.bind (liftResult (core.slice.index.Slice.index
  (core.slice.index.SliceIndexRangeUsizeSlice U8) proof ⟨start,finish⟩)) fun selected =>
 NMX_R8_VerifierUse241.source s publicBytes.to_slice selected checkpoint

theorem array_length (b : Array U8 1880#usize) : Slice.len b.to_slice = 1880#usize := by
 apply UScalar.eq_of_val_eq
 rw [NMX_R2_LengthGuard.value]
 exact b.property

theorem factor (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (proof checkpoint : Slice U8)
 (start finish : Usize) (pub : Array U8 1880#usize) :
 NMX_R8_Factor241.afterEncode (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices)
  v proof checkpoint start finish pub = source v.statement proof checkpoint start finish pub := by
 unfold NMX_R8_Factor241.afterEncode
 change RSL.Spec.bind (RSL.Spec.pure pub.to_slice) _ = _
 rw [RSL.Spec.bind_pure,NMX_R8_Std241.statement]
 change RSL.Spec.bind (RSL.Spec.pure 1880#usize) _ = _
 rw [RSL.Spec.bind_pure,array_length]
 change RSL.Spec.bind (RSL.Spec.pure pub.to_slice) _ = _
 rw [RSL.Spec.bind_pure]
 unfold source
 apply congrArg (RSL.Spec.bind _)
 funext selected
 rw [NMX_R8_Std241.observer]
 change RSL.Spec.bind (RSL.Spec.pure none) _ = _
 rw [RSL.Spec.bind_pure]
 unfold NMX_R8_VerifierUse241.source NMS_R2N_RawTry.literal
 apply congrArg (RSL.Spec.bind _)
 funext verifierReply
 apply congrArg (RSL.Spec.bind _)
 funext programReply
 apply congrArg (RSL.Spec.bind _)
 funext flow
 cases flow <;> rfl
#print axioms array_length
#print axioms factor
end NMX_R8_EncodedFactor241
end
