import NEG_DotsTypes.Funs
import RPz7_FIp_NativeDots
set_option autoImplicit false
noncomputable section
namespace NEG_DotAssociation
open Aeneas Aeneas.Std Result AspisR1
/-- Literal emitted body equality, including both loop functions and every
checked read/update. The nine callee interpretations are installed explicitly
in NEG_DotsTypes.FunsExternal; their native transport/domains remain separate. -/
theorem emitted_to_cohort (q : Array U8 608#usize)
    (g : Array FIo_Native.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) :
    NEG_DotsTypes.fast_dots.four_dots_one q g slot =
      FIp_NativeDots.fast_dots.four_dots_one q g slot := by rfl
#print axioms emitted_to_cohort
end NEG_DotAssociation
end
