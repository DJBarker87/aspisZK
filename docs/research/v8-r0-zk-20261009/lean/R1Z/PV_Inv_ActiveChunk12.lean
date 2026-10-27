import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk12
open R0P
/-- Generated terminal descriptor snapshot, entries 48..51.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073520, 3, 12, ⟨731, 0, 1⟩, ⟨748, 0, 1⟩⟩,
  ⟨1124073521, 4, 12, ⟨731, 1, 1⟩, ⟨736, 0, 10⟩⟩,
  ⟨1124073522, 3, 13, ⟨747, 0, 1⟩, ⟨764, 0, 1⟩⟩,
  ⟨1124073523, 4, 13, ⟨747, 1, 1⟩, ⟨752, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk12
