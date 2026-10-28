import NDO_JGw_Values9
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line9
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values9.value.val[j.val]'(by rw [JGw_Values9.value.property];exact j.isLt)) := by
  fin_cases j
  · change (594231039<2147483647 ∧ 1768961454<2147483647 ∧ 1584022688<2147483647 ∧ 262305210<2147483647) ∧ (1497600569<2147483647 ∧ 1037168300<2147483647 ∧ 1395967439<2147483647 ∧ 1039079598<2147483647)
    omega
  · change (1504351165<2147483647 ∧ 389464337<2147483647 ∧ 1673641914<2147483647 ∧ 919002449<2147483647) ∧ (1955910997<2147483647 ∧ 794125224<2147483647 ∧ 328630422<2147483647 ∧ 135755893<2147483647)
    omega
  · change (36575841<2147483647 ∧ 362686844<2147483647 ∧ 1584107066<2147483647 ∧ 844875834<2147483647) ∧ (2070399795<2147483647 ∧ 1671459129<2147483647 ∧ 1732952581<2147483647 ∧ 291883057<2147483647)
    omega
  · change (37725191<2147483647 ∧ 1856947094<2147483647 ∧ 1016008733<2147483647 ∧ 1707136693<2147483647) ∧ (1962004440<2147483647 ∧ 1786102911<2147483647 ∧ 528433090<2147483647 ∧ 327217950<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values9.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values9.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line9
end
