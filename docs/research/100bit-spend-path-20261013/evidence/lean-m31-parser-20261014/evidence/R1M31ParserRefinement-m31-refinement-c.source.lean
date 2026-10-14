import R1ExtractedM31Parser
import AeneasWordCodec

/-! Refine the extracted current M31 parser against the retained four-byte
canonical decoder, using the existing Aeneas U32 little-endian bridge. -/
set_option autoImplicit false

namespace AspisR1.M31ParserRefinement

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec

def wordArray (bytes : WordBytes) : Array U8 4#usize :=
  Array.make 4#usize
    [AspisV8R19.SqueezeOracleBridge.encodeByte (bytes 0),
     AspisV8R19.SqueezeOracleBridge.encodeByte (bytes 1),
     AspisV8R19.SqueezeOracleBridge.encodeByte (bytes 2),
     AspisV8R19.SqueezeOracleBridge.encodeByte (bytes 3)]

def valueToU32 (value : M31Value) : U32 :=
  U32.ofNatCore value.val (by
    have hvalue := value.isLt
    norm_num [m31Modulus, rawCandidateCount] at hvalue
    norm_num [UScalarTy.numBits]
    omega)

private theorem valueToU32_val (value : M31Value) :
    (valueToU32 value).val = value.val := by
  simp [valueToU32]

private theorem extractedP_val : AspisR1M31Parser.field.P.val = m31Modulus := by
  rw [AspisR1M31Parser.field.P]
  norm_num [m31Modulus, rawCandidateCount]

theorem from_le_bytes_refines (bytes : WordBytes) :
    AspisR1M31Parser.field.M31.from_le_bytes (wordArray bytes) =
      Result.ok ((decodeM31LE bytes).map valueToU32) := by
  have hread : core.num.U32.from_le_bytes (wordArray bytes) =
      AspisR1.AeneasWordCodec.aeneasWord bytes := by
    rfl
  have hbranch :
      (AspisR1.AeneasWordCodec.aeneasWord bytes >= AspisR1M31Parser.field.P) ↔
        m31Modulus ≤ (decodeWordLE bytes).val := by
    change AspisR1M31Parser.field.P.val ≤
      (AspisR1.AeneasWordCodec.aeneasWord bytes).val ↔ _
    rw [extractedP_val, AspisR1.AeneasWordCodec.aeneasWord_val_eq]
  unfold AspisR1M31Parser.field.M31.from_le_bytes
  rw [hread]
  simp only [lift, bind_tc_ok]
  simp only [hbranch]
  by_cases hcanonical : (decodeWordLE bytes).val < m31Modulus
  · have hnot : ¬ m31Modulus ≤ (decodeWordLE bytes).val := by omega
    simp only [if_neg hnot, decodeM31LE, dif_pos hcanonical, Option.map_some]
    apply congrArg Result.ok
    apply congrArg some
    apply UScalar.eq_of_val_eq
    rw [AspisR1.AeneasWordCodec.aeneasWord_val_eq, valueToU32_val]
    rfl
  · have hnoncanonical : m31Modulus ≤ (decodeWordLE bytes).val := by omega
    simp only [if_pos hnoncanonical, decodeM31LE, dif_neg hcanonical, Option.map_none]

#print axioms from_le_bytes_refines

end AspisR1.M31ParserRefinement
