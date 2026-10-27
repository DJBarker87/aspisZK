import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk29
open R0P
/-- Generated terminal descriptor snapshot, entries 116..119.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073588, 0, 0, ⟨982, 0, 1⟩, ⟨348, 0, 1⟩⟩,
  ⟨1124073589, 0, 0, ⟨982, 1, 13⟩, ⟨336, 0, 10⟩⟩,
  ⟨1124073590, 0, 0, ⟨347, 0, 1⟩, ⟨985, 0, 12⟩⟩,
  ⟨1124073591, 0, 0, ⟨986, 0, 1⟩, ⟨364, 0, 1⟩⟩
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
end R1Z.PV_Inv_ActiveChunk29
