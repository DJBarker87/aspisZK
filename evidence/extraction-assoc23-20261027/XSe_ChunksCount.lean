import XSe_ValidatorFold
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ChunksCount
/-- Exact count including arbitrary ignored tails. -/
theorem source (bs : List U8) :
 (List.toChunksExact 32 (by decide) bs).1.length=bs.length/32 := by
 rw [List.toChunksExact]
 split
 · rename_i short
   simp only [List.length_nil]
   exact (Nat.div_eq_of_lt short).symm
 · rename_i full
   simp only [List.length_cons]
   rw [source (bs.drop 32)]
   simp only [List.length_drop]
   omega
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega
#print axioms source
end XSe_ChunksCount
