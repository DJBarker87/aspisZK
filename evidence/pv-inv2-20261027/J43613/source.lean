import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk09
open R0P
/-- Generated terminal descriptor snapshot, entries 36..39.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073508, 3, 6, ⟨635, 0, 1⟩, ⟨652, 0, 1⟩⟩,
  ⟨1124073509, 4, 6, ⟨635, 1, 1⟩, ⟨640, 0, 10⟩⟩,
  ⟨1124073510, 3, 7, ⟨651, 0, 1⟩, ⟨668, 0, 1⟩⟩,
  ⟨1124073511, 4, 7, ⟨651, 1, 1⟩, ⟨656, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk09
