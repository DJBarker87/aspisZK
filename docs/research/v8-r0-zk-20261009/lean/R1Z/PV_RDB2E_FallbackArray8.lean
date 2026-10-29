import R1Z.PV_RDB2E_FallbackArrayRead

section
-- Unchanged source component R1Z.PV_CBL_FallbackArray8
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackArray8
set_option autoImplicit false
abbrev A8 := Array U32 8#usize
def pack (w0 w1 w2 w3 w4 w5 w6 w7 : U32) : A8 := ⟨[w0,w1,w2,w3,w4,w5,w6,w7],by simp⟩
theorem index0 (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7) 0#usize = ok w0 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index1 (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7) 1#usize = ok w1 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index2 (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7) 2#usize = ok w2 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index3 (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7) 3#usize = ok w3 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index4 (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7) 4#usize = ok w4 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index5 (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7) 5#usize = ok w5 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index6 (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7) 6#usize = ok w6 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index7 (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7) 7#usize = ok w7 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
#print axioms pack
#print axioms index0
#print axioms index1
#print axioms index2
#print axioms index3
#print axioms index4
#print axioms index5
#print axioms index6
#print axioms index7
end R1Z.PV_CBL_FallbackArray8

end
