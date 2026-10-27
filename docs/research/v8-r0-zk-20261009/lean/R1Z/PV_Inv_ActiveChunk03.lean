import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk03
open R0P
/-- Generated terminal descriptor snapshot, entries 12..15.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073484, 1, 0, ⟨460, 0, 6⟩, ⟨1010, 0, 7⟩⟩,
  ⟨1124073485, 0, 0, ⟨508, 0, 6⟩, ⟨1012, 0, 7⟩⟩,
  ⟨1124073486, 0, 0, ⟨1008, 0, 7⟩, ⟨1014, 0, 6⟩⟩,
  ⟨1124073487, 0, 0, ⟨1010, 0, 7⟩, ⟨1014, 1, 8⟩⟩
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
end R1Z.PV_Inv_ActiveChunk03
