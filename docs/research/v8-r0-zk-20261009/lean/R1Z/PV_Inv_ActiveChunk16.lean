import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk16
open R0P
/-- Generated terminal descriptor snapshot, entries 64..67.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073536, 0, 0, ⟨59, 0, 1⟩, ⟨913, 0, 12⟩⟩,
  ⟨1124073537, 0, 0, ⟨914, 0, 1⟩, ⟨76, 0, 1⟩⟩,
  ⟨1124073538, 0, 0, ⟨914, 1, 13⟩, ⟨64, 0, 10⟩⟩,
  ⟨1124073539, 0, 0, ⟨75, 0, 1⟩, ⟨917, 0, 12⟩⟩
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
end R1Z.PV_Inv_ActiveChunk16
