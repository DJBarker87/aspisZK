import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk18
open R0P
/-- Generated terminal descriptor snapshot, entries 72..75.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073544, 0, 0, ⟨922, 1, 13⟩, ⟨96, 0, 10⟩⟩,
  ⟨1124073545, 0, 0, ⟨107, 0, 1⟩, ⟨925, 0, 12⟩⟩,
  ⟨1124073546, 0, 0, ⟨926, 0, 1⟩, ⟨124, 0, 1⟩⟩,
  ⟨1124073547, 0, 0, ⟨926, 1, 13⟩, ⟨112, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk18
