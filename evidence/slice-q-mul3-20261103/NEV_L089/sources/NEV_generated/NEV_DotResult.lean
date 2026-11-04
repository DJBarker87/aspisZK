import NEG_DotAssociation
set_option autoImplicit false
noncomputable section
namespace NEV_DotResult
open Aeneas Aeneas.Std Result AspisR1
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact
/-- Literal generated inner-step association, all Result and control tags. -/
theorem inner (q : Array U8 608#usize) (g : Array E 29#usize) (slot : Usize)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize) :
    NEG_DotsTypes.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums := rfl
/-- Complete actual generated caller Result is the adopted cohort Result.
This reuses NEG unchanged; no success or preselected child value is assumed. -/
theorem source (q : Array U8 608#usize) (g : Array E 29#usize) (slot : Usize) :
    NEG_DotsTypes.fast_dots.four_dots_one q g slot=
      FIp_NativeDots.fast_dots.four_dots_one q g slot :=
  NEG_DotAssociation.emitted_to_cohort q g slot
/-- External ghost state/effects follow the COMPLETE Result, including fail/div.
Physical caller/callee frames and native StepBy transport remain separate. -/
theorem result_state_effects {S Event : Type} (state : S)
    (q : Array U8 608#usize) (g : Array E 29#usize) (slot : Usize) :
    (do let result ← NEG_DotsTypes.fast_dots.four_dots_one q g slot
        ok (result,state,([] : List Event))) =
      (do let result ← FIp_NativeDots.fast_dots.four_dots_one q g slot
          ok (result,state,([] : List Event))) := by rw [source]
#print axioms inner
#print axioms source
#print axioms result_state_effects
end NEV_DotResult
end
