import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk28
open R0P
/-- Generated terminal descriptor snapshot, entries 112..115.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073584, 0, 0, ⟨315, 0, 1⟩, ⟨977, 0, 12⟩⟩,
  ⟨1124073585, 0, 0, ⟨978, 0, 1⟩, ⟨332, 0, 1⟩⟩,
  ⟨1124073586, 0, 0, ⟨978, 1, 13⟩, ⟨320, 0, 10⟩⟩,
  ⟨1124073587, 0, 0, ⟨331, 0, 1⟩, ⟨981, 0, 12⟩⟩
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
end R1Z.PV_Inv_ActiveChunk28
