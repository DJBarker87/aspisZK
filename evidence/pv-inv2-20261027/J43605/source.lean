import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk01
open R0P
/-- Generated terminal descriptor snapshot, entries 4..7.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073476, 1, 0, ⟨459, 0, 0⟩, ⟨464, 0, 0⟩⟩,
  ⟨1124073477, 0, 0, ⟨491, 0, 0⟩, ⟨496, 0, 0⟩⟩,
  ⟨1124073478, 0, 0, ⟨507, 0, 0⟩, ⟨512, 0, 0⟩⟩,
  ⟨1124073479, 0, 0, ⟨11, 0, 1⟩, ⟨28, 0, 1⟩⟩
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
end R1Z.PV_Inv_ActiveChunk01
