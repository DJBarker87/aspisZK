import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveChunk31
open R0P
/-- Generated terminal descriptor snapshot, entries 124..127.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  ⟨1124073596, 0, 0, ⟨379, 0, 1⟩, ⟨993, 0, 12⟩⟩,
  ⟨1124073597, 0, 0, ⟨994, 0, 1⟩, ⟨396, 0, 1⟩⟩,
  ⟨1124073598, 0, 0, ⟨994, 1, 13⟩, ⟨384, 0, 10⟩⟩,
  ⟨1124073599, 0, 0, ⟨395, 0, 1⟩, ⟨997, 0, 12⟩⟩
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
end R1Z.PV_Inv_ActiveChunk31
