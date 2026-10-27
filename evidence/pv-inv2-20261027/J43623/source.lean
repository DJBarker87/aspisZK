import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk19
open R0P
/-- Generated terminal descriptor snapshot, entries 76..79.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073548, 0, 0, ⟨123, 0, 1⟩, ⟨929, 0, 12⟩⟩,
  ⟨1124073549, 0, 0, ⟨930, 0, 1⟩, ⟨140, 0, 1⟩⟩,
  ⟨1124073550, 0, 0, ⟨930, 1, 13⟩, ⟨128, 0, 10⟩⟩,
  ⟨1124073551, 0, 0, ⟨139, 0, 1⟩, ⟨933, 0, 12⟩⟩
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
end R1Z.PV_Inv_ActiveChunk19
