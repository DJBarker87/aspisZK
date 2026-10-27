import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk33
open R0P
/-- Generated terminal descriptor snapshot, entries 132..135.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073604, 0, 0, ⟨1002, 1, 13⟩, ⟨880, 0, 10⟩⟩,
  ⟨1124073605, 0, 0, ⟨891, 0, 1⟩, ⟨1005, 0, 12⟩⟩,
  ⟨1124073606, 0, 0, ⟨1006, 0, 1⟩, ⟨908, 0, 1⟩⟩,
  ⟨1124073607, 0, 0, ⟨1006, 1, 13⟩, ⟨896, 0, 10⟩⟩
]

theorem active (l : CopyLink) (hl : l ∈ links) :
    CopyActiveRow l.producer.row ∧ CopyActiveRow l.consumer.row := by
  simp only [links,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  all_goals constructor <;> rfl

theorem tag_bound (l : CopyLink) (hl : l ∈ links) : l.tag < 2147483647 := by
  simp only [links,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> decide

#print axioms active
#print axioms tag_bound
end R1Z.PV_Inv_ActiveChunk33
