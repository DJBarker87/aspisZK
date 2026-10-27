import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk23
open R0P
/-- Generated terminal descriptor snapshot, entries 92..95.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073564, 0, 0, ⟨950, 0, 1⟩, ⟨220, 0, 1⟩⟩,
  ⟨1124073565, 0, 0, ⟨950, 1, 13⟩, ⟨208, 0, 10⟩⟩,
  ⟨1124073566, 0, 0, ⟨219, 0, 1⟩, ⟨953, 0, 12⟩⟩,
  ⟨1124073567, 0, 0, ⟨954, 0, 1⟩, ⟨236, 0, 1⟩⟩
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
end R1Z.PV_Inv_ActiveChunk23
