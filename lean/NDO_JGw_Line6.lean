import NDO_JGw_Values6
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line6
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values6.value.val[j.val]'(by rw [JGw_Values6.value.property];exact j.isLt)) := by
  fin_cases j
  · change (494412570<2147483647 ∧ 1427631101<2147483647 ∧ 5260489<2147483647 ∧ 277573310<2147483647) ∧ (364466490<2147483647 ∧ 400123641<2147483647 ∧ 2092986464<2147483647 ∧ 176710615<2147483647)
    omega
  · change (1396410589<2147483647 ∧ 253103824<2147483647 ∧ 812667064<2147483647 ∧ 1952677907<2147483647) ∧ (422301239<2147483647 ∧ 1782981050<2147483647 ∧ 462977955<2147483647 ∧ 1206238169<2147483647)
    omega
  · change (1438858277<2147483647 ∧ 100051946<2147483647 ∧ 1191364192<2147483647 ∧ 1434773302<2147483647) ∧ (346749938<2147483647 ∧ 600437687<2147483647 ∧ 490465501<2147483647 ∧ 1967594027<2147483647)
    omega
  · change (1730837807<2147483647 ∧ 842207747<2147483647 ∧ 667964143<2147483647 ∧ 1938842104<2147483647) ∧ (139811795<2147483647 ∧ 57078191<2147483647 ∧ 1583247013<2147483647 ∧ 1380695758<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values6.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values6.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line6
end
