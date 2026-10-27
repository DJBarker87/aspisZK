import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk04
open R0P
/-- Generated terminal descriptor snapshot, entries 16..19.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073488, 0, 0, ⟨1012, 0, 7⟩, ⟨1015, 0, 8⟩⟩,
  ⟨1124073489, 0, 0, ⟨1014, 0, 9⟩, ⟨1015, 1, 6⟩⟩,
  ⟨1124073490, 0, 0, ⟨64, 0, 10⟩, ⟨1017, 0, 11⟩⟩,
  ⟨1124073491, 0, 0, ⟨913, 0, 6⟩, ⟨1017, 1, 7⟩⟩
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
end R1Z.PV_Inv_ActiveChunk04
