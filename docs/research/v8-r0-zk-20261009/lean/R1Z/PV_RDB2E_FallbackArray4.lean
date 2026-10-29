import R1Z.PV_RDB2E_FallbackRound
import R1Z.PV_RDB2D_SHAModel

section
-- Unchanged source component R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackArray4
set_option autoImplicit false
abbrev A4 := Array U32 4#usize
def pack (a b c d : U32) : A4 := ⟨[a,b,c,d],by simp⟩
theorem index0 (a b c d : U32) : Array.index_usize (pack a b c d) 0#usize = ok a := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index1 (a b c d : U32) : Array.index_usize (pack a b c d) 1#usize = ok b := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index2 (a b c d : U32) : Array.index_usize (pack a b c d) 2#usize = ok c := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
theorem index3 (a b c d : U32) : Array.index_usize (pack a b c d) 3#usize = ok d := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,pack]
#print axioms pack
#print axioms index0
#print axioms index1
#print axioms index2
#print axioms index3
end R1Z.PV_CBL_FallbackArray4

end
