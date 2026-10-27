import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk14
open R0P
/-- Generated terminal descriptor snapshot, entries 56..59.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073528, 3, 16, ⟨795, 0, 1⟩, ⟨812, 0, 1⟩⟩,
  ⟨1124073529, 4, 16, ⟨795, 1, 1⟩, ⟨800, 0, 10⟩⟩,
  ⟨1124073530, 3, 17, ⟨811, 0, 1⟩, ⟨828, 0, 1⟩⟩,
  ⟨1124073531, 4, 17, ⟨811, 1, 1⟩, ⟨816, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk14
