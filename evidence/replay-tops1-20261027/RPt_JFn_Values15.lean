import RPt_JFn_Value15_0
import RPt_JFn_Value15_1
import RPt_JFn_Value15_2
import RPt_JFn_Value15_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values15
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value15_0.value,SAQ_RecordDecode.fromRecord JFn_Value15_1.value,SAQ_RecordDecode.fromRecord JFn_Value15_2.value,SAQ_RecordDecode.fromRecord JFn_Value15_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨15,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨15,by decide⟩ _ _ _ _
    JFn_Value15_0.source JFn_Value15_1.source JFn_Value15_2.source JFn_Value15_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value15_0.value) := by
  change (1749639170<2147483647 ∧ 1290136797<2147483647 ∧ 221955118<2147483647 ∧ 583088708<2147483647) ∧ (454101661<2147483647 ∧ 30355175<2147483647 ∧ 1908354380<2147483647 ∧ 1743188521<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value15_1.value) := by
  change (2125733106<2147483647 ∧ 1095027047<2147483647 ∧ 2055831088<2147483647 ∧ 1391136258<2147483647) ∧ (2135643119<2147483647 ∧ 539335121<2147483647 ∧ 24058997<2147483647 ∧ 1962945445<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value15_2.value) := by
  change (525804773<2147483647 ∧ 383663845<2147483647 ∧ 2054336180<2147483647 ∧ 977361562<2147483647) ∧ (2145639217<2147483647 ∧ 2006113668<2147483647 ∧ 1042851790<2147483647 ∧ 746334419<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value15_3.value) := by
  change (770560448<2147483647 ∧ 1880496115<2147483647 ∧ 912993931<2147483647 ∧ 2090132334<2147483647) ∧ (846412175<2147483647 ∧ 827636172<2147483647 ∧ 105495798<2147483647 ∧ 1533028336<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 2#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value15_2.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values15
end
