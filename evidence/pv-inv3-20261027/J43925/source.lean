import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk25
open R0P
/-- Generated terminal descriptor snapshot, entries 100..103.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073572, 0, 0, ⟨251, 0, 1⟩, ⟨961, 0, 12⟩⟩,
  ⟨1124073573, 0, 0, ⟨962, 0, 1⟩, ⟨268, 0, 1⟩⟩,
  ⟨1124073574, 0, 0, ⟨962, 1, 13⟩, ⟨256, 0, 10⟩⟩,
  ⟨1124073575, 0, 0, ⟨267, 0, 1⟩, ⟨965, 0, 12⟩⟩
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
end R1Z.PV_Inv_ActiveChunk25
