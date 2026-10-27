import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk08
open R0P
/-- Generated terminal descriptor snapshot, entries 32..35.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073504, 3, 4, ⟨603, 0, 1⟩, ⟨620, 0, 1⟩⟩,
  ⟨1124073505, 4, 4, ⟨603, 1, 1⟩, ⟨608, 0, 10⟩⟩,
  ⟨1124073506, 3, 5, ⟨619, 0, 1⟩, ⟨636, 0, 1⟩⟩,
  ⟨1124073507, 4, 5, ⟨619, 1, 1⟩, ⟨624, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk08
