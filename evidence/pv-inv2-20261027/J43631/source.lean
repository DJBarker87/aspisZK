import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk27
open R0P
/-- Generated terminal descriptor snapshot, entries 108..111.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073580, 0, 0, ⟨970, 1, 13⟩, ⟨288, 0, 10⟩⟩,
  ⟨1124073581, 0, 0, ⟨299, 0, 1⟩, ⟨973, 0, 12⟩⟩,
  ⟨1124073582, 0, 0, ⟨974, 0, 1⟩, ⟨316, 0, 1⟩⟩,
  ⟨1124073583, 0, 0, ⟨974, 1, 13⟩, ⟨304, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk27
