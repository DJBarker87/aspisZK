import NDO_JGw_Values7
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Line7
open Aeneas Aeneas.Std Result

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (JGw_Values7.value.val[j.val]'(by rw [JGw_Values7.value.property];exact j.isLt)) := by
  fin_cases j
  · change (1455069336<2147483647 ∧ 44819172<2147483647 ∧ 1218322180<2147483647 ∧ 1351758312<2147483647) ∧ (178743778<2147483647 ∧ 243044163<2147483647 ∧ 1790351735<2147483647 ∧ 1889787775<2147483647)
    omega
  · change (600865669<2147483647 ∧ 1760543780<2147483647 ∧ 1643193913<2147483647 ∧ 1050852917<2147483647) ∧ (1700349525<2147483647 ∧ 550772394<2147483647 ∧ 529185211<2147483647 ∧ 326904698<2147483647)
    omega
  · change (1656677859<2147483647 ∧ 519419504<2147483647 ∧ 1794599757<2147483647 ∧ 820488980<2147483647) ∧ (1435165728<2147483647 ∧ 666249457<2147483647 ∧ 421867039<2147483647 ∧ 613764257<2147483647)
    omega
  · change (1624881175<2147483647 ∧ 334229555<2147483647 ∧ 1231804413<2147483647 ∧ 2095236360<2147483647) ∧ (394298181<2147483647 ∧ 127601937<2147483647 ∧ 180333677<2147483647 ∧ 1814595571<2147483647)
    omega
#print axioms canonical

theorem source (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values7.value inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 canonical
#print axioms source

def value (inverse : Array U32 5#usize) : SAQ_WideABI.E := Classical.choose (source inverse)
theorem returned (inverse : Array U32 5#usize) :
    SAQ_LineQuery.line JFq_Alpha1.scalar JGw_Values7.value inverse=ok (value inverse) :=
  (Classical.choose_spec (source inverse)).1
#print axioms returned
end AspisR1.JGw_Line7
end
