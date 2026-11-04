import NEI_FourWrapperLaw
import NEV_DotInputs
set_option autoImplicit false
noncomputable section
namespace NEV_FourResult
open Aeneas Aeneas.Std Result AspisR1
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact
/-- Reuse the actual NEI extraction, all Result tags and SAME four calls. -/
theorem source (q : Slice U8) (g : Array E 29#usize) :
 NEI_FourWrapper.fast_dots.four_dots q g=FIp_NativeDots.fast_dots.four_dots q g :=
 NEI_FourWrapperLaw.emitted_to_cohort q g

theorem result_state_effects {S Event : Type} (state : S) (q : Slice U8) (g : Array E 29#usize) :
 (do let out ← NEI_FourWrapper.fast_dots.four_dots q g
     ok (out,state,([] : List Event)))=
 (do let out ← FIp_NativeDots.fast_dots.four_dots q g
     ok (out,state,([] : List Event))) := by rw [source]
/-- Each literal call establishes the slot domain. g is the SAME immutable
argument, so its canonical coordinate domain is preserved for every call. -/
theorem calls (g : NEV_DotInputs.Coefficients) (canonical : NEV_DotInputs.Canonical g) :
 ∀ slot∈([0,1,2,3] : List Nat),slot<4 ∧ NEV_DotInputs.Canonical g := by
 intro slot member
 exact ⟨NEI_FourWrapperLaw.slots slot member,canonical⟩
#print axioms source
#print axioms result_state_effects
#print axioms calls
end NEV_FourResult
end
