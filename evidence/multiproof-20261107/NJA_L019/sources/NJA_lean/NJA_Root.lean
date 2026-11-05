import NJA_Reads
import MultiproofConeByteEquality
import MultiproofConeRootGuard

set_option autoImplicit false
noncomputable section
namespace NJA_Root
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

-- Complete helper result, including the native fixed first-value selection.
theorem result (values : Array (Array U8 32#usize) 16#usize) (root : Array U8 32#usize) :
    NJA_Multiproof.multiproof.root_matches values root =
      ok (decide ((values.val[0]'(by have len : values.val.length=16 := values.property; omega)) = root)) := by
  rw [NJA_Reads.root_result]
  exact AspisR1.MultiproofConeByteEquality.array_eq_total _ _

-- The adopted terminal guard contains the SAME comparison alongside n/index/cursor.
-- This equation does not infer verifier acceptance from root equality.
theorem cohort_comparison (s : MultiproofConeRef.reference.Scratch)
    (root : Array U8 32#usize) :
    NJA_Multiproof.multiproof.root_matches s.val root =
      ok (decide (s.val.val[0]! = root)) := by
  rw [result]
  congr 2
  exact (getElem!_pos s.val.val 0 (by have len : s.val.val.length=16 := s.val.property; omega)).symm

#print axioms result
#print axioms cohort_comparison
end NJA_Root
end
