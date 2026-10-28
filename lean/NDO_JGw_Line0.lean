import NDO_JGw_Values0
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line0
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values0.value.val[j.val]'(by rw [JGw_Values0.value.property];exact j.isLt)) := by
  fin_cases j
  · change (1320773618<2147483647 ∧ 1877397073<2147483647 ∧ 1270151964<2147483647 ∧ 305062365<2147483647) ∧ (1020420403<2147483647 ∧ 915035097<2147483647 ∧ 599194724<2147483647 ∧ 1817990359<2147483647)
    omega
  · change (1563861204<2147483647 ∧ 1072163658<2147483647 ∧ 411747604<2147483647 ∧ 1798218478<2147483647) ∧ (1109478725<2147483647 ∧ 1870686468<2147483647 ∧ 771145124<2147483647 ∧ 708078029<2147483647)
    omega
  · change (1021480397<2147483647 ∧ 229375840<2147483647 ∧ 1188872916<2147483647 ∧ 1965336302<2147483647) ∧ (1059617637<2147483647 ∧ 452497105<2147483647 ∧ 253464645<2147483647 ∧ 987991798<2147483647)
    omega
  · change (95730862<2147483647 ∧ 1359327733<2147483647 ∧ 1229841427<2147483647 ∧ 1475802313<2147483647) ∧ (1309751629<2147483647 ∧ 1193187707<2147483647 ∧ 670744641<2147483647 ∧ 1839779700<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values0.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values0.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line0
end
