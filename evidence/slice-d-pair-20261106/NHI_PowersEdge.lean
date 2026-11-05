import NHI_PowersReuse
set_option autoImplicit false
namespace NHI_PowersEdge
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- The SAME canonical alpha produces the SAME four powers consumed by scalar.
The inherited CLOSED producer is imported, not re-proved or rerun natively. -/
theorem scalar (alpha : NE) (ha : canonE alpha) (f : Array NQ 4#usize)
 (hf : ∀ x∈f.val,canonQ x) :
 ∃ p out,FIo_Native.weights.powers 4#usize alpha=ok p ∧
 (∀ x∈p.val,canonE x) ∧
 FIo_Native.weights.Weights.scalar_factor f p=ok out ∧ canonE out := by
 obtain ⟨p,hp,model,cp⟩ := NFW_PowersCohort.source 4#usize alpha ha
 obtain ⟨sum,out,fold,cs,run,co,values⟩ := NHI_Scalar.total f p cp hf
 exact ⟨p,out,hp,cp,run,co⟩

#print axioms scalar
end NHI_PowersEdge
