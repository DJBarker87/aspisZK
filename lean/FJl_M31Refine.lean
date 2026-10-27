import FJi_DecodeM31
import R1M31ParserRefinement
import R1ExactLeafFieldCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_M31Refine
open Aeneas Aeneas.Std Result
open RetainedFieldByteCodec
/-- Installed source M31 parser and the existing scalar parser have the SAME
body, guards and bytes. -/
theorem source (a : Array U8 4#usize) :
    FIp_DotDecode.field.M31.from_le_bytes a=AspisR1M31Parser.field.M31.from_le_bytes a := by
  simp only [FIp_DotDecode.field.M31.from_le_bytes,AspisR1M31Parser.field.M31.from_le_bytes,
    FIp_DotDecode.field.P,AspisR1M31Parser.field.P]
/-- Byte-function version of strict literal scalar decoding. -/
theorem value (bytes : WordBytes) (x : U32)
    (run : FIp_DotDecode.field.M31.from_le_bytes (M31ParserRefinement.wordArray bytes)=ok (some x)) :
    ExactLeafFieldCodec.decodeM31 (List.ofFn bytes)=some (x.val : ExactLeafFieldCodec.M31Exact) := by
  rw [source,M31ParserRefinement.from_le_bytes_refines] at run
  have eq := Result.ok.inj run
  cases hd : decodeM31LE bytes with
  | none => simp only [hd,Option.map_none,reduceCtorEq] at eq
  | some v =>
    simp only [hd,Option.map_some,Option.some.injEq] at eq
    subst x
    simp only [ExactLeafFieldCodec.decodeM31,decodeM31Bytes,ListFieldCodec.fixedBytes?_ofFn,
      Option.bind_some,hd,Option.map_some]
    congr 1
    apply ZMod.val_injective
    rw [M31ParserRefinement.valueToU32_val,ZMod.val_natCast_of_lt v.isLt]
    rfl
#print axioms source
#print axioms value
end AspisR1.FJl_M31Refine
end
