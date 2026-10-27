import R1Z.PV_Inv_ActiveRegistry
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskSource
open R0P

def rows : List (Fin 1024) := copyLinks.flatMap (fun l => [l.producer.row,l.consumer.row])

/-- OR ignores endpoint multiplicity and enumeration order; the installed
schedule/registry row equality is still P_registry. Sorted/dedup source calls
must identify their row set, rather than asserting a mask by its fingerprint. -/
def mask (block : Fin 64) : Nat :=
  rows.foldl (fun acc r => if r.val / 16=block.val then acc ||| (2^(r.val%16)) else acc) 0

theorem rows_active (r : Fin 1024) (hr : r ∈ rows) : CopyActiveRow r := by
  obtain ⟨l,hl,he⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  · exact (PV_Inv_ActiveRegistry.active l hl).1
  · exact (PV_Inv_ActiveRegistry.active l hl).2

#print axioms rows_active
end R1Z.PV_Inv_MaskSource
