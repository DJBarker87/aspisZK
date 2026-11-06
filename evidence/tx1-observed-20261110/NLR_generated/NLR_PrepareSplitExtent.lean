import NLR_PrepareDenote
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareSplitExtent
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Library split law at the SAME owned Vec slice. The length guard is a
pre-state fact, not inferred from successful semantic verification. -/
theorem split (bytes : Slice U8) (cut : Usize) (bound : cut ≤ bytes.length)
 (parts : (Slice U8 × Slice U8) × ((Slice U8 × Slice U8) → Slice U8))
 (call : core.slice.Slice.split_at_mut bytes cut = ok parts) :
 parts.1.1.length=cut.val ∧ parts.1.2.length=bytes.length-cut.val := by
 obtain ⟨pair,actual,facts⟩ := WP.spec_imp_exists
  (core.slice.Slice.split_at_mut.spec bytes cut bound)
 have same : pair=parts := Result.ok.inj (actual.symm.trans call)
 subst pair
 exact ⟨facts.1,facts.2.1⟩
/-- Concrete13831/928 source split extents, including the complete14759-byte guard.
The SAME allocation's total length is required; a successful allocator is not
silently supplied. -/
theorem semantic (bytes : Slice U8) (size : bytes.length=14759)
 (parts : (Slice U8 × Slice U8) × ((Slice U8 × Slice U8) → Slice U8))
 (call : core.slice.Slice.split_at_mut bytes 13831#usize = ok parts) :
 parts.1.1.val.length=13831 ∧ parts.1.2.val.length=928 := by
 obtain ⟨first,second⟩ := split bytes 13831#usize (by change 13831≤bytes.length;omega) parts call
 exact ⟨first,by change parts.1.2.length=928;omega⟩
#print axioms split
#print axioms semantic
end AspisR1.NLR_PrepareSplitExtent
end
