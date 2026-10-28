import R1Z.PV_CB_Op71Funs
import R1Z.ProverCommitWordBytes47
import AeneasWordCodec
set_option autoImplicit false
namespace PV_L2C_CanonicalParser
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71
/-- The real scalar byte primitives, rather than a codec-success premise. -/
theorem word_roundtrip (x : U32) :
    core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x)=x := by
  let bs := AspisR1.RetainedFieldByteCodec.encodeWordLE (R1Z.ProverCommitWordBytes47.rawWord x)
  have raw_eq : R1Z.ProverCommitWordBytes47.rawByte=AspisV8R19.SqueezeOracleBridge.decodeByte := by
    funext b
    apply Fin.ext
    rfl
  have hb : (core.num.U32.to_le_bytes x).val.map AspisV8R19.SqueezeOracleBridge.decodeByte=
      List.ofFn bs := by
    simpa only [raw_eq] using R1Z.ProverCommitWordBytes47.word x
  have injective : Function.Injective AspisV8R19.SqueezeOracleBridge.decodeByte := by
    intro a b h
    rw [← AspisV8R19.SqueezeOracleBridge.word_roundtrip a,
      ← AspisV8R19.SqueezeOracleBridge.word_roundtrip b,h]
  have hs : (core.num.U32.to_le_bytes x).val=
      [AspisV8R19.SqueezeOracleBridge.encodeByte (bs 0),
       AspisV8R19.SqueezeOracleBridge.encodeByte (bs 1),
       AspisV8R19.SqueezeOracleBridge.encodeByte (bs 2),
       AspisV8R19.SqueezeOracleBridge.encodeByte (bs 3)] := by
    apply List.map_injective injective
    rw [hb]
    simp only [List.map_cons,List.map_nil,AspisV8R19.SqueezeOracleBridge.byte_roundtrip]
    rfl
  have ha : core.num.U32.to_le_bytes x=Array.make 4#usize
      [AspisV8R19.SqueezeOracleBridge.encodeByte (bs 0),
       AspisV8R19.SqueezeOracleBridge.encodeByte (bs 1),
       AspisV8R19.SqueezeOracleBridge.encodeByte (bs 2),
       AspisV8R19.SqueezeOracleBridge.encodeByte (bs 3)] := Subtype.ext hs
  apply UScalar.eq_of_val_eq
  rw [ha]
  change (AspisR1.AeneasWordCodec.aeneasWord bs).val=x.val
  rw [AspisR1.AeneasWordCodec.aeneasWord_val_eq]
  change (AspisR1.RetainedFieldByteCodec.decodeWordLE
    (AspisR1.RetainedFieldByteCodec.encodeWordLE (R1Z.ProverCommitWordBytes47.rawWord x))).val=x.val
  rw [AspisR1.RetainedFieldByteCodec.decodeWordLE_encodeWordLE]
  rfl
#print axioms word_roundtrip

/-- The actual extracted native >=P branch takes its accepting arm. -/
theorem scalar_parse (x : U32) (hx : x.val<2147483647) :
    aspis_core.field.M31.from_le_bytes (core.num.U32.to_le_bytes x)=ok (some x) := by
  have h : ¬ x≥aspis_core.field.P := by
    unfold aspis_core.field.P
    scalar_tac
  unfold aspis_core.field.M31.from_le_bytes
  rw [word_roundtrip]
  change (if x≥aspis_core.field.P then ok none else ok (some x))=ok (some x)
  rw [if_neg h]
#print axioms scalar_parse
end PV_L2C_CanonicalParser
