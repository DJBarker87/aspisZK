import NDO_JGw_Values1
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line1
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values1.value.val[j.val]'(by rw [JGw_Values1.value.property];exact j.isLt)) := by
  fin_cases j
  · change (1456580399<2147483647 ∧ 841726080<2147483647 ∧ 979224028<2147483647 ∧ 1847754340<2147483647) ∧ (1212465351<2147483647 ∧ 709231024<2147483647 ∧ 279512060<2147483647 ∧ 1739500556<2147483647)
    omega
  · change (3946788<2147483647 ∧ 1921141621<2147483647 ∧ 1912846855<2147483647 ∧ 81146261<2147483647) ∧ (944397719<2147483647 ∧ 1465743260<2147483647 ∧ 691618691<2147483647 ∧ 1876781494<2147483647)
    omega
  · change (1129387613<2147483647 ∧ 315607019<2147483647 ∧ 1673928397<2147483647 ∧ 1452954405<2147483647) ∧ (1916289967<2147483647 ∧ 1075044692<2147483647 ∧ 688894222<2147483647 ∧ 1221141249<2147483647)
    omega
  · change (8292422<2147483647 ∧ 1571991281<2147483647 ∧ 44036622<2147483647 ∧ 293227156<2147483647) ∧ (256204945<2147483647 ∧ 2020339820<2147483647 ∧ 378728118<2147483647 ∧ 301896724<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values1.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values1.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line1
end
