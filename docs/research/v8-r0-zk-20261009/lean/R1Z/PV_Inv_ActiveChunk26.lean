import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk26
open R0P
/-- Generated terminal descriptor snapshot, entries 104..107.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073576, 0, 0, ⟨966, 0, 1⟩, ⟨284, 0, 1⟩⟩,
  ⟨1124073577, 0, 0, ⟨966, 1, 13⟩, ⟨272, 0, 10⟩⟩,
  ⟨1124073578, 0, 0, ⟨283, 0, 1⟩, ⟨969, 0, 12⟩⟩,
  ⟨1124073579, 0, 0, ⟨970, 0, 1⟩, ⟨300, 0, 1⟩⟩
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
end R1Z.PV_Inv_ActiveChunk26
