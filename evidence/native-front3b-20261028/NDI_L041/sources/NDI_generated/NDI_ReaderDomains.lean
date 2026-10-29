import Aeneas
set_option autoImplicit false
namespace NDI_ReaderDomains
open Aeneas Aeneas.Std Result

theorem queries (i : Nat) (active : i<22) : 320+4*i+4≤1736 := by omega

theorem semantic_alpha (i : Nat) (active : i<10) : 408+16*i+16≤1736 := by omega

theorem weights (i : Nat) (active : i<64) : 712+16*i+16≤1736 := by omega

theorem structural (offset width : Nat)
    (member : (offset,width)∈[(80,32),(112,32),(144,32),(176,32),(208,32),
      (240,32),(272,32),(304,16),(568,16),(584,16),(600,16),(616,16),
      (632,32),(664,32),(696,16)]) : offset+width≤1736 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> omega

theorem end_position : 712+16*64=1736 ∧ 1736+32=1768 := by omega

theorem native_fit (bytes : Slice U8) (offset width coordinate : Usize)
    (backing : bytes.val.length=1768) (body : offset.val+width.val≤1736)
    (selected : coordinate.val<width.val) :
    offset.val≤bytes.val.length ∧ width.val≤bytes.val.length-offset.val ∧
      offset.val+coordinate.val<bytes.val.length := by omega

#print axioms queries
#print axioms semantic_alpha
#print axioms weights
#print axioms structural
#print axioms end_position
#print axioms native_fit
end NDI_ReaderDomains
