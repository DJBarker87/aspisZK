import MultiproofConeWordScan
import R1M31ParserArray
import OraclePortCompactDraft

set_option autoImplicit false
namespace AspisR1.MultiproofConeEndian
open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec

/-- Reuse the retained all-input M31 parser theorem, including rejection;
no canonical-operand premise is introduced at the byte boundary. -/
theorem strict_word_iff (a : Array U8 4#usize) :
    (core.num.U32.from_le_bytes a).val < 2147483647 ↔
      (decodeWordLE (M31ParserArray.arrayBytes a)).val < 2147483647 := by
  have h := M31ParserArray.parser_refines_array a
  unfold AspisR1M31Parser.field.M31.from_le_bytes AspisR1M31Parser.field.P at h
  simp only [lift, bind_tc_ok, UScalar.le_equiv,
    show (2147483647#u32).val = 2147483647 from rfl] at h
  have order : 2147483647 ≤ (core.num.U32.from_le_bytes a).val ↔
      ¬ (core.num.U32.from_le_bytes a).val < 2147483647 := by omega
  simp only [order] at h
  by_cases hs : (core.num.U32.from_le_bytes a).val < 2147483647 <;>
    by_cases hm : (decodeWordLE (M31ParserArray.arrayBytes a)).val < 2147483647 <;>
    simp_all [decodeM31LE, m31Modulus, rawCandidateCount] <;> omega

/-- Four-byte mathematical little-endian framing is the retained word codec. -/
theorem little_four (b : WordBytes) :
    OraclePortCompactDraft.little (List.ofFn b) = (decodeWordLE b).val := by
  simp [List.ofFn_succ, OraclePortCompactDraft.little, decodeWordLE]
  ring

#print axioms strict_word_iff
#print axioms little_four
end AspisR1.MultiproofConeEndian
