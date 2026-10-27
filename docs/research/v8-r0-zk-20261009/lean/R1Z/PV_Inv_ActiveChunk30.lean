import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk30
open R0P
/-- Generated terminal descriptor snapshot, entries 120..123.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073592, 0, 0, ⟨986, 1, 13⟩, ⟨352, 0, 10⟩⟩,
  ⟨1124073593, 0, 0, ⟨363, 0, 1⟩, ⟨989, 0, 12⟩⟩,
  ⟨1124073594, 0, 0, ⟨990, 0, 1⟩, ⟨380, 0, 1⟩⟩,
  ⟨1124073595, 0, 0, ⟨990, 1, 13⟩, ⟨368, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk30
