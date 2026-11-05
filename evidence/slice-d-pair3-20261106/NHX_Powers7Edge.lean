import NHI_PowersReuse
set_option autoImplicit false
namespace NHX_Powers7Edge
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- The final fold consumes exactly powers7 of the SAME canonical kappa.
NFW's native domain explicitly contains7; no extension from powers4 is used. -/
theorem source (kappa : NE) (hk : canonE kappa) :
 ∃ powers : Array NE 7#usize,FIo_Native.weights.powers 7#usize kappa=ok powers ∧
 (∀ x∈powers.val,canonE x) := by
 obtain ⟨powers,run,model,canonical⟩:=NFW_PowersCohort.source 7#usize kappa hk
 exact ⟨powers,run,canonical⟩

#print axioms source
end NHX_Powers7Edge
