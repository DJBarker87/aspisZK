import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk11
open R0P
/-- Generated terminal descriptor snapshot, entries 44..47.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073516, 3, 10, ⟨699, 0, 1⟩, ⟨716, 0, 1⟩⟩,
  ⟨1124073517, 4, 10, ⟨699, 1, 1⟩, ⟨704, 0, 10⟩⟩,
  ⟨1124073518, 3, 11, ⟨715, 0, 1⟩, ⟨732, 0, 1⟩⟩,
  ⟨1124073519, 4, 11, ⟨715, 1, 1⟩, ⟨720, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk11
