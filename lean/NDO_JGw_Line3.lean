import NDO_JGw_Values3
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line3
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values3.value.val[j.val]'(by rw [JGw_Values3.value.property];exact j.isLt)) := by
  fin_cases j
  · change (1654760959<2147483647 ∧ 1780566121<2147483647 ∧ 1145494261<2147483647 ∧ 819486776<2147483647) ∧ (480012192<2147483647 ∧ 1675691627<2147483647 ∧ 1336652276<2147483647 ∧ 1865860444<2147483647)
    omega
  · change (1056851884<2147483647 ∧ 1665049839<2147483647 ∧ 1624045842<2147483647 ∧ 1818324685<2147483647) ∧ (572854969<2147483647 ∧ 186035269<2147483647 ∧ 667382904<2147483647 ∧ 1556558713<2147483647)
    omega
  · change (782984098<2147483647 ∧ 116858813<2147483647 ∧ 1881615806<2147483647 ∧ 859035786<2147483647) ∧ (951340756<2147483647 ∧ 1723451480<2147483647 ∧ 399757087<2147483647 ∧ 1183503165<2147483647)
    omega
  · change (1345579330<2147483647 ∧ 252607270<2147483647 ∧ 2100509967<2147483647 ∧ 628802256<2147483647) ∧ (245603780<2147483647 ∧ 1844768942<2147483647 ∧ 1576033504<2147483647 ∧ 1382024442<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values3.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values3.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line3
end
