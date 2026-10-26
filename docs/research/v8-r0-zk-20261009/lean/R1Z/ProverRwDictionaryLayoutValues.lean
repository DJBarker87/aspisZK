import R1Z.ProverRwDictionaryLayout
import R1Z.ProverRwDictionaryLayoutTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryLayoutValues
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- This is a fixed, acyclic 24-declaration layout expression, not a recurrence
-- or a large finite enumeration. All intermediate machine values fit Usize.
theorem logical_semantic (ops : ExternalFuns) :
    (ProverRwDictionaryLayout.selected ops).op241 = .ok 13831#usize := by
  rw [ProverRwDictionaryLayout.entry241]
  exact ProverRwDictionaryLayoutTotal.r22_compact_LOGICAL_SEMANTIC_total

theorem proof_bytes (ops : ExternalFuns) :
    (ProverRwDictionaryLayout.selected ops).op242 = .ok 57607#usize := by
  rw [ProverRwDictionaryLayout.entry242]
  exact ProverRwDictionaryLayoutTotal.r22_compact_PROOF_BYTES_total

theorem node_offset (ops : ExternalFuns) :
    (ProverRwDictionaryLayout.selected ops).op243 = .ok 28359#usize := by
  rw [ProverRwDictionaryLayout.entry243]
  exact ProverRwDictionaryLayoutTotal.r22_compact_OFF_NODES_total

theorem opening_offset (ops : ExternalFuns) :
    (ProverRwDictionaryLayout.selected ops).op244 = .ok 10055#usize := by
  rw [ProverRwDictionaryLayout.entry244]
  exact ProverRwDictionaryLayoutTotal.r22_compact_OFF_OPENINGS_total

#print axioms logical_semantic
#print axioms proof_bytes
#print axioms node_offset
#print axioms opening_offset
end R1Z.ProverRwDictionaryLayoutValues
