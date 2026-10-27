import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk00
open R0P
/-- Generated terminal descriptor snapshot, entries 0..3.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073472, 0, 0, ⟨27, 0, 0⟩, ⟨32, 0, 0⟩⟩,
  ⟨1124073473, 0, 0, ⟨43, 0, 0⟩, ⟨48, 0, 0⟩⟩,
  ⟨1124073474, 0, 0, ⟨411, 0, 0⟩, ⟨416, 0, 0⟩⟩,
  ⟨1124073475, 1, 0, ⟨443, 0, 0⟩, ⟨448, 0, 0⟩⟩
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
end R1Z.PV_Inv_ActiveChunk00
