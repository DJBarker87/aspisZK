import S2SdkProofComparatorV1
set_option autoImplicit false
noncomputable section
namespace NJI_StdNe
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

def ne {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
 (b : Slice T) (a : Array U N) : Result Bool :=
 core.slice.cmp.PartialEqSlice.ne cmp b a.to_slice

/-- Pinned P7 byte comparison; reuse the canonical theorem on arbitrary slices. -/
theorem value {N : Usize} (b : Slice U8) (a : Array U8 N) :
 ne core.cmp.PartialEqU8 b a = ok (decide (b.val ≠ a.val)) := by
 exact AspisS2OwnedStage1.SdkReference.ProofGate.standard_ne b a.to_slice
#print axioms value
end NJI_StdNe
