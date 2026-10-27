import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk24
open R0P
/-- Generated terminal descriptor snapshot, entries 96..99.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073568, 0, 0, ⟨954, 1, 13⟩, ⟨224, 0, 10⟩⟩,
  ⟨1124073569, 0, 0, ⟨235, 0, 1⟩, ⟨957, 0, 12⟩⟩,
  ⟨1124073570, 0, 0, ⟨958, 0, 1⟩, ⟨252, 0, 1⟩⟩,
  ⟨1124073571, 0, 0, ⟨958, 1, 13⟩, ⟨240, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk24
