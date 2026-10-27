import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk20
open R0P
/-- Generated terminal descriptor snapshot, entries 80..83.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073552, 0, 0, ⟨934, 0, 1⟩, ⟨156, 0, 1⟩⟩,
  ⟨1124073553, 0, 0, ⟨934, 1, 13⟩, ⟨144, 0, 10⟩⟩,
  ⟨1124073554, 0, 0, ⟨155, 0, 1⟩, ⟨937, 0, 12⟩⟩,
  ⟨1124073555, 0, 0, ⟨938, 0, 1⟩, ⟨172, 0, 1⟩⟩
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
end R1Z.PV_Inv_ActiveChunk20
