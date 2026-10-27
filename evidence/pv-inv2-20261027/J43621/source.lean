import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk17
open R0P
/-- Generated terminal descriptor snapshot, entries 68..71.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073540, 0, 0, ⟨918, 0, 1⟩, ⟨92, 0, 1⟩⟩,
  ⟨1124073541, 0, 0, ⟨918, 1, 13⟩, ⟨80, 0, 10⟩⟩,
  ⟨1124073542, 0, 0, ⟨91, 0, 1⟩, ⟨921, 0, 12⟩⟩,
  ⟨1124073543, 0, 0, ⟨922, 0, 1⟩, ⟨108, 0, 1⟩⟩
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
end R1Z.PV_Inv_ActiveChunk17
