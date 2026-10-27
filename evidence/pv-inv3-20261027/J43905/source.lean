import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk05
open R0P
/-- Generated terminal descriptor snapshot, entries 20..23.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073492, 1, 0, ⟨523, 0, 1⟩, ⟨1018, 0, 11⟩⟩,
  ⟨1124073493, 1, 0, ⟨475, 0, 1⟩, ⟨540, 0, 1⟩⟩,
  ⟨1124073494, 2, 0, ⟨523, 1, 1⟩, ⟨540, 1, 1⟩⟩,
  ⟨1124073495, 0, 0, ⟨1018, 0, 11⟩, ⟨528, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk05
