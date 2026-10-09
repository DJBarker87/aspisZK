import AspisR515SharedGamma.SharedGammaDots
import AspisR523GammaGroupExecution.R523GammaGroupExecution

set_option autoImplicit false
namespace AspisV8R19.R528PartitionSelected28Terms
open AspisV8.SharedGammaDots

/-- The seven selected groups of four terms flatten in source index order. -/
theorem selected28_groups_flatten {T : Type*} (terms : Fin 28 → T) :
    (List.ofFn (fun k : Fin 7 =>
      List.ofFn (fun j : Fin 4 => terms ⟨4*k.val+j.val, by omega⟩))).flatten =
      List.ofFn terms := by
  simp [List.ofFn_succ]

/-- The selected one-based source slots of the seven four-term groups are in
range. -/
theorem selected28_source_slots (k : Fin 7) (j : Fin 4) :
    1 + 4*k.val + j.val < 29 := by
  exact (source_indices k.val j.val k.isLt j.isLt).2.1

#print axioms selected28_groups_flatten
#print axioms selected28_source_slots
end AspisV8R19.R528PartitionSelected28Terms
