import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailChunkArrayEquality
open Aeneas Aeneas.Std

def makeChunk (out : Array U8 32#usize) (offset : Nat) (hoff : offset + 4 ≤ 32) : Array U8 4#usize :=
  Array.make 4#usize [
    out.val[offset]'(by have h := out.property; change out.val.length = 32 at h; omega),
    out.val[offset + 1]'(by have h := out.property; change out.val.length = 32 at h; omega),
    out.val[offset + 2]'(by have h := out.property; change out.val.length = 32 at h; omega),
    out.val[offset + 3]'(by have h := out.property; change out.val.length = 32 at h; omega)]

theorem makeChunk_eq_of_getElem?
    (out : Array U8 32#usize) (bytes : Array U8 4#usize)
    (offset : Nat) (hoff : offset + 4 ≤ 32)
    (hchunk : ∀ k : Nat, (hk : k < 4) →
      out.val[offset + k]'(by
        have hlen : out.val.length = 32 := by have h := out.property; change out.val.length = 32 at h; exact h
        rw [hlen]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk offset) hoff) =
      bytes.val[k]'(by
        have hlen : bytes.val.length = 4 := by have h := bytes.property; change bytes.val.length = 4 at h; exact h
        rw [hlen]
        exact hk)) :
    makeChunk out offset hoff = bytes := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [makeChunk, Array.make, bytes.property]
  · intro i hi hj
    have hi4 : i < 4 := by simpa [bytes.property] using hj
    have hiCase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hiCase with rfl | rfl | rfl | rfl
    · have h := hchunk 0 (by omega)
      simpa [makeChunk, Array.make] using h
    · have h := hchunk 1 (by omega)
      simpa [makeChunk, Array.make] using h
    · have h := hchunk 2 (by omega)
      simpa [makeChunk, Array.make] using h
    · have h := hchunk 3 (by omega)
      simpa [makeChunk, Array.make] using h

#print axioms makeChunk_eq_of_getElem?
end AspisR1PairForestLaneEncoderTailChunkArrayEquality
