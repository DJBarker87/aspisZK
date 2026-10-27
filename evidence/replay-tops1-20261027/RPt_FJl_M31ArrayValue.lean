import RPt_FJl_M31Refine
import RPt_FJl_ByteArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_M31ArrayValue
open Aeneas Aeneas.Std Result
/-- Strict source-to-literal M31 VALUE for arbitrary source bytes. -/
theorem value (a : Array U8 4#usize) (x : U32)
    (run : FIp_DotDecode.field.M31.from_le_bytes a=ok (some x)) :
    ExactLeafFieldCodec.decodeM31 (MultiproofConeCanonical.bytesOf a.val)=
      some (x.val : ExactLeafFieldCodec.M31Exact) := by
  rw [←FJl_ByteArray.source a] at run
  have h := FJl_M31Refine.value (M31ParserArray.arrayBytes a) x run
  rwa [FJl_ByteArray.list] at h
#print axioms value
end AspisR1.FJl_M31ArrayValue
end
