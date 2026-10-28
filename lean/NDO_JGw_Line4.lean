import NDO_JGw_Values4
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line4
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values4.value.val[j.val]'(by rw [JGw_Values4.value.property];exact j.isLt)) := by
  fin_cases j
  · change (671337488<2147483647 ∧ 1901021208<2147483647 ∧ 497274848<2147483647 ∧ 1331167961<2147483647) ∧ (1381240697<2147483647 ∧ 1835046799<2147483647 ∧ 703737261<2147483647 ∧ 346517556<2147483647)
    omega
  · change (1610806253<2147483647 ∧ 1950016415<2147483647 ∧ 1387353283<2147483647 ∧ 1122721168<2147483647) ∧ (1778923990<2147483647 ∧ 776654507<2147483647 ∧ 735539447<2147483647 ∧ 2024481296<2147483647)
    omega
  · change (245097044<2147483647 ∧ 604007735<2147483647 ∧ 472816414<2147483647 ∧ 790316287<2147483647) ∧ (814641984<2147483647 ∧ 733474112<2147483647 ∧ 679597612<2147483647 ∧ 815958365<2147483647)
    omega
  · change (1733495406<2147483647 ∧ 1006483110<2147483647 ∧ 1825086166<2147483647 ∧ 254379937<2147483647) ∧ (2096922458<2147483647 ∧ 1310138954<2147483647 ∧ 1695658189<2147483647 ∧ 716103946<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values4.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values4.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line4
end
