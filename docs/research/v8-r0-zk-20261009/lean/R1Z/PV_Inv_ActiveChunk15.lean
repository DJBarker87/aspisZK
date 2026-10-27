import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk15
open R0P
/-- Generated terminal descriptor snapshot, entries 60..63.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073532, 3, 18, ⟨827, 0, 1⟩, ⟨844, 0, 1⟩⟩,
  ⟨1124073533, 4, 18, ⟨827, 1, 1⟩, ⟨832, 0, 10⟩⟩,
  ⟨1124073534, 3, 19, ⟨843, 0, 1⟩, ⟨860, 0, 1⟩⟩,
  ⟨1124073535, 4, 19, ⟨843, 1, 1⟩, ⟨848, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk15
