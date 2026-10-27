import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk13
open R0P
/-- Generated terminal descriptor snapshot, entries 52..55.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073524, 3, 14, ⟨763, 0, 1⟩, ⟨780, 0, 1⟩⟩,
  ⟨1124073525, 4, 14, ⟨763, 1, 1⟩, ⟨768, 0, 10⟩⟩,
  ⟨1124073526, 3, 15, ⟨779, 0, 1⟩, ⟨796, 0, 1⟩⟩,
  ⟨1124073527, 4, 15, ⟨779, 1, 1⟩, ⟨784, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk13
