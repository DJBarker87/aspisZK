import NDO_JGw_Values8
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line8
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values8.value.val[j.val]'(by rw [JGw_Values8.value.property];exact j.isLt)) := by
  fin_cases j
  · change (664030414<2147483647 ∧ 274126781<2147483647 ∧ 590864128<2147483647 ∧ 719124115<2147483647) ∧ (1728643651<2147483647 ∧ 48422914<2147483647 ∧ 883504869<2147483647 ∧ 1901254830<2147483647)
    omega
  · change (769210404<2147483647 ∧ 57844669<2147483647 ∧ 1216294227<2147483647 ∧ 947911936<2147483647) ∧ (1314863630<2147483647 ∧ 516026130<2147483647 ∧ 1593396871<2147483647 ∧ 1484342503<2147483647)
    omega
  · change (191870746<2147483647 ∧ 398001530<2147483647 ∧ 1107537619<2147483647 ∧ 699826812<2147483647) ∧ (1058797636<2147483647 ∧ 422078492<2147483647 ∧ 1230196429<2147483647 ∧ 1600095536<2147483647)
    omega
  · change (1375473218<2147483647 ∧ 315401171<2147483647 ∧ 2100493293<2147483647 ∧ 1209606237<2147483647) ∧ (161341447<2147483647 ∧ 200761296<2147483647 ∧ 1539652433<2147483647 ∧ 521665819<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values8.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values8.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line8
end
