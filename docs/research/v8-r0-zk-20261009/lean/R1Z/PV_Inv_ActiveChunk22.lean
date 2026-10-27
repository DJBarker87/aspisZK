import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk22
open R0P
/-- Generated terminal descriptor snapshot, entries 88..91.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073560, 0, 0, ⟨187, 0, 1⟩, ⟨945, 0, 12⟩⟩,
  ⟨1124073561, 0, 0, ⟨946, 0, 1⟩, ⟨204, 0, 1⟩⟩,
  ⟨1124073562, 0, 0, ⟨946, 1, 13⟩, ⟨192, 0, 10⟩⟩,
  ⟨1124073563, 0, 0, ⟨203, 0, 1⟩, ⟨949, 0, 12⟩⟩
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
end R1Z.PV_Inv_ActiveChunk22
