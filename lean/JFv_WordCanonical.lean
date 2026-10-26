import JFv_QM31
import MultiproofConeEndian
set_option autoImplicit false
namespace AspisR1.JFv_WordCanonical
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeCanonical

theorem bytes (arr : Array U8 4#usize) :
    List.ofFn (M31ParserArray.arrayBytes arr) = bytesOf arr.val := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,bytesOf,List.length_map,arr.property,show (4#usize).val=4 from rfl]
  · intro i hi hj
    simp only [List.getElem_ofFn,M31ParserArray.arrayBytes,bytesOf,List.getElem_map]

theorem bound (arr : Array U8 4#usize) (canonical : canonical (bytesOf arr.val)) :
    (core.num.U32.from_le_bytes arr).val < 2147483647 := by
  rw [MultiproofConeEndian.strict_word_iff,←MultiproofConeEndian.little_four,bytes]
  have h := canonical.2 0 (by simp only [List.mem_range,bytesOf,List.length_map,arr.property];decide)
  have len : (bytesOf arr.val).length ≤ 4 := by
    simp only [bytesOf,List.length_map,arr.property];decide
  simpa only [slice,Nat.mul_zero,List.drop_zero,List.take_of_length_le len] using h

#print axioms bytes
#print axioms bound
end AspisR1.JFv_WordCanonical
