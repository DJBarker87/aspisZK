import RPt_JFo_Prepared
import SAQ_LineQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_AlphaCanonical
open Aeneas Aeneas.Std Result

theorem alpha1 : Port4C_QueryArithmetic.CanonE JFq_Alpha1.scalar := by
  change (1923325677<2147483647 ∧ 606708475<2147483647 ∧ 390399940<2147483647 ∧ 1424274113<2147483647) ∧
    (1600018693<2147483647 ∧ 561365806<2147483647 ∧ 1230057896<2147483647 ∧ 509172918<2147483647)
  omega

#print axioms alpha1
end AspisR1.JFn_AlphaCanonical
end
