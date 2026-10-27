import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk21
open R0P
/-- Generated terminal descriptor snapshot, entries 84..87.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073556, 0, 0, ⟨938, 1, 13⟩, ⟨160, 0, 10⟩⟩,
  ⟨1124073557, 0, 0, ⟨171, 0, 1⟩, ⟨941, 0, 12⟩⟩,
  ⟨1124073558, 0, 0, ⟨942, 0, 1⟩, ⟨188, 0, 1⟩⟩,
  ⟨1124073559, 0, 0, ⟨942, 1, 13⟩, ⟨176, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk21
