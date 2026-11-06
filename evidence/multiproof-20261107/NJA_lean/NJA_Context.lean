import NJA_Root
import NJA_CohortArity
import MultiproofConeRef.Funs

set_option autoImplicit false
noncomputable section
namespace NJA_Context
open Aeneas Aeneas.Std Result NJA_Multiproof
attribute [local instance] Classical.propDecidable

-- Substitution is under an arbitrary continuation, preserving all Result
-- branches and any state/log carried by the continuation's result type.
theorem bits {α : Type} (k : U32 → Result α) :
 (do let b ← multiproof.Arity.bits .Two; k b) = k 1#u32 := rfl

theorem width {α : Type} (k : Usize → Result α) :
 (do let w ← multiproof.Arity.width .Two; k w) = k 2#usize := by
 rw [NJA_Arity.two_width]
 rfl

theorem levels {α : Type} (k : U32 → Result α) :
 (do let h ← multiproof.Arity.levels .Two; k h) = k 18#u32 := by
 rw [NJA_Arity.two_levels]
 rfl

theorem index {α : Type} (s : MultiproofConeRef.reference.Scratch)
 (i : Usize) (k : U32 → Result α) :
 (do let x ← multiproof.index_at s.idx i; k x) =
 (do let x ← Array.index_usize s.idx i; k x) := rfl

theorem root {α : Type} (s : MultiproofConeRef.reference.Scratch)
 (r : Array U8 32#usize) (k : Bool → Result α) :
 (do let b ← multiproof.root_matches s.val r; k b) =
 k (decide (s.val.val[0]! = r)) := by
 rw [NJA_Root.cohort_comparison]
 rfl

#print axioms bits
#print axioms width
#print axioms levels
#print axioms index
#print axioms root
end NJA_Context
end
