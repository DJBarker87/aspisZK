import R1Z.PV_CBL_FallbackArrayRead
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackArray16
set_option autoImplicit false
abbrev A16 := Array U32 16#usize
def pack (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) : A16 := ⟨[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15],by simp⟩
theorem index0 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 0#usize = ok w0 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index1 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 1#usize = ok w1 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index2 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 2#usize = ok w2 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index3 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 3#usize = ok w3 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index4 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 4#usize = ok w4 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index5 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 5#usize = ok w5 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index6 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 6#usize = ok w6 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index7 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 7#usize = ok w7 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index8 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 8#usize = ok w8 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index9 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 9#usize = ok w9 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index10 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 10#usize = ok w10 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index11 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 11#usize = ok w11 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index12 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 12#usize = ok w12 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index13 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 13#usize = ok w13 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index14 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 14#usize = ok w14 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index15 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    Array.index_usize (pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 15#usize = ok w15 := by
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
#print axioms index8
#print axioms index9
#print axioms index10
#print axioms index11
#print axioms index12
#print axioms index13
#print axioms index14
#print axioms index15
end R1Z.PV_CBL_FallbackArray16
