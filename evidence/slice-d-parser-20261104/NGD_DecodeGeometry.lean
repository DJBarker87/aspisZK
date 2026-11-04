import NGD_DecodeGuards
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_DecodeGeometry
/-- Caller establishes these bounds from the actual checked range, with no
canonicality or final-decoder-success premise. -/
theorem fitting (len off n i : Nat) (minlen : 5 ≤ len) (cap : len ≤ 3717)
    (positive : 0 < n) (live : i < n) (range : 32*off + 32*n ≤ len-5) :
    off+i < 116 ∧ 5+32*off+32*i+32 ≤ len ∧
    32*off+32*i+16 ≤ len-5 ∧ off+n ≤ 116 := by omega

/-- ChunksExact's selected low sixteen bytes are the same original payload
window as the indexed emitted decoder. -/
theorem selected_low (bytes : List U8) (off n i : Nat) (live : i < n) :
    ((((bytes.drop (32*off)).take (32*n)).drop (32*i)).take 32).take 16 =
      (bytes.drop (32*(off+i))).take 16 := by
  simp only [List.take_take,List.drop_take,List.drop_drop]
  have h : min 16 (min 32 (32*n-32*i)) = 16 := by omega
  simp only [h]
  congr 2 <;> omega

/-- Framing is removed once; no replacement payload is introduced. -/
theorem framed_low (bytes : List U8) (off i : Nat) :
    ((bytes.drop 5).drop (32*(off+i))).take 16 =
      (bytes.drop (5+32*off+32*i)).take 16 := by
  simp only [List.drop_drop]
  congr 2 <;> omega

/-- The Q decoder sees exactly sixteen bytes on every reached source step. -/
theorem low_length (bytes : List U8) (off n i : Nat) (live : i<n)
    (range : 32*off+32*n ≤ bytes.length) :
    ((bytes.drop (32*(off+i))).take 16).length = 16 := by
  simp only [List.length_take,List.length_drop]
  omega
#print axioms fitting
#print axioms selected_low
#print axioms framed_low
#print axioms low_length
end NGD_DecodeGeometry
