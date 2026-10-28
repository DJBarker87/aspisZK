import NDO_JGw_Values5
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line5
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values5.value.val[j.val]'(by rw [JGw_Values5.value.property];exact j.isLt)) := by
  fin_cases j
  · change (2060537896<2147483647 ∧ 1418268399<2147483647 ∧ 124297972<2147483647 ∧ 1643810385<2147483647) ∧ (1177585472<2147483647 ∧ 785366786<2147483647 ∧ 451118307<2147483647 ∧ 1920921062<2147483647)
    omega
  · change (176288459<2147483647 ∧ 886246977<2147483647 ∧ 2145784843<2147483647 ∧ 55600143<2147483647) ∧ (962097383<2147483647 ∧ 1554768102<2147483647 ∧ 1399764748<2147483647 ∧ 111971848<2147483647)
    omega
  · change (175834614<2147483647 ∧ 813019672<2147483647 ∧ 597567193<2147483647 ∧ 934878347<2147483647) ∧ (885784028<2147483647 ∧ 1067922863<2147483647 ∧ 1691122957<2147483647 ∧ 1819234992<2147483647)
    omega
  · change (902812610<2147483647 ∧ 1541094360<2147483647 ∧ 1607722716<2147483647 ∧ 1463071865<2147483647) ∧ (1651209600<2147483647 ∧ 1859119510<2147483647 ∧ 467514766<2147483647 ∧ 410267422<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values5.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values5.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line5
end
