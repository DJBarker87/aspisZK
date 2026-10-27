import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk07
open R0P
/-- Generated terminal descriptor snapshot, entries 28..31.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073500, 3, 2, ⟨571, 0, 1⟩, ⟨588, 0, 1⟩⟩,
  ⟨1124073501, 4, 2, ⟨571, 1, 1⟩, ⟨576, 0, 10⟩⟩,
  ⟨1124073502, 3, 3, ⟨587, 0, 1⟩, ⟨604, 0, 1⟩⟩,
  ⟨1124073503, 4, 3, ⟨587, 1, 1⟩, ⟨592, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk07
