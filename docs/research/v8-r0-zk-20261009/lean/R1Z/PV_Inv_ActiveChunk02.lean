import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk02
open R0P
/-- Generated terminal descriptor snapshot, entries 8..11.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073480, 0, 0, ⟨12, 0, 1⟩, ⟨412, 0, 1⟩⟩,
  ⟨1124073481, 0, 0, ⟨44, 0, 2⟩, ⟨428, 0, 3⟩⟩,
  ⟨1124073482, 0, 0, ⟨60, 0, 4⟩, ⟨428, 1, 5⟩⟩,
  ⟨1124073483, 0, 0, ⟨44, 1, 6⟩, ⟨1008, 0, 7⟩⟩
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
end R1Z.PV_Inv_ActiveChunk02
