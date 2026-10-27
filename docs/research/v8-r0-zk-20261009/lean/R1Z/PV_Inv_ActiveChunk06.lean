import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk06
open R0P
/-- Generated terminal descriptor snapshot, entries 24..27.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073496, 3, 0, ⟨539, 0, 1⟩, ⟨556, 0, 1⟩⟩,
  ⟨1124073497, 4, 0, ⟨539, 1, 1⟩, ⟨544, 0, 10⟩⟩,
  ⟨1124073498, 3, 1, ⟨555, 0, 1⟩, ⟨572, 0, 1⟩⟩,
  ⟨1124073499, 4, 1, ⟨555, 1, 1⟩, ⟨560, 0, 10⟩⟩
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
end R1Z.PV_Inv_ActiveChunk06
