import NDO_JGw_Values2
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line2
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values2.value.val[j.val]'(by rw [JGw_Values2.value.property];exact j.isLt)) := by
  fin_cases j
  · change (1033882084<2147483647 ∧ 1752908335<2147483647 ∧ 1661726728<2147483647 ∧ 493637179<2147483647) ∧ (1121358450<2147483647 ∧ 2062438048<2147483647 ∧ 1867820851<2147483647 ∧ 453558728<2147483647)
    omega
  · change (1590511308<2147483647 ∧ 1201712515<2147483647 ∧ 1174844659<2147483647 ∧ 177624340<2147483647) ∧ (73257167<2147483647 ∧ 1788406020<2147483647 ∧ 1896995077<2147483647 ∧ 1817016679<2147483647)
    omega
  · change (1020750806<2147483647 ∧ 2008592790<2147483647 ∧ 1441332143<2147483647 ∧ 1949526172<2147483647) ∧ (1093750194<2147483647 ∧ 551010874<2147483647 ∧ 2041841295<2147483647 ∧ 1087379731<2147483647)
    omega
  · change (2105904998<2147483647 ∧ 1610425956<2147483647 ∧ 641719873<2147483647 ∧ 1829180105<2147483647) ∧ (146852901<2147483647 ∧ 1495337783<2147483647 ∧ 1441999667<2147483647 ∧ 1898936014<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values2.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values2.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line2
end
