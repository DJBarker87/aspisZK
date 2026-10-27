import XSe_ChunksCount
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ChunksWindow
/-- Every actual standard chunk is the same chronological32-byte model window. -/
theorem source (bs : List U8) (i : Nat) (chunk : List U8)
 (read : (List.toChunksExact 32 (by decide) bs).1[i]?=some chunk) :
 chunk=(bs.drop (32*i)).take 32 := by
 rw [List.toChunksExact] at read
 split at read
 · cases i <;> simp at read
 · cases i with
   | zero =>
     simp only [List.getElem?_cons_zero] at read
     cases Option.some.inj read
     simp only [Nat.mul_zero,List.drop_zero]
   | succ i =>
     simp only [List.getElem?_cons_succ] at read
     rw [source (bs.drop 32) i chunk read]
     simp only [List.drop_drop,Nat.mul_succ]
     congr 2
     omega
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega
#print axioms source
end XSe_ChunksWindow
