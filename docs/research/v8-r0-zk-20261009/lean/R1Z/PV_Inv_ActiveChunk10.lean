import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk10
open R0P
/-- Generated terminal descriptor snapshot, entries 40..43.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073512, 3, 8, ⟨667, 0, 1⟩, ⟨684, 0, 1⟩⟩,
  ⟨1124073513, 4, 8, ⟨667, 1, 1⟩, ⟨672, 0, 10⟩⟩,
  ⟨1124073514, 3, 9, ⟨683, 0, 1⟩, ⟨700, 0, 1⟩⟩,
  ⟨1124073515, 4, 9, ⟨683, 1, 1⟩, ⟨688, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk10
