import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk32
open R0P
/-- Generated terminal descriptor snapshot, entries 128..131.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073600, 0, 0, ⟨998, 0, 1⟩, ⟨876, 0, 1⟩⟩,
  ⟨1124073601, 0, 0, ⟨998, 1, 13⟩, ⟨864, 0, 10⟩⟩,
  ⟨1124073602, 0, 0, ⟨875, 0, 1⟩, ⟨1001, 0, 12⟩⟩,
  ⟨1124073603, 0, 0, ⟨1002, 0, 1⟩, ⟨892, 0, 1⟩⟩
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
end R1Z.PV_Inv_ActiveChunk32
