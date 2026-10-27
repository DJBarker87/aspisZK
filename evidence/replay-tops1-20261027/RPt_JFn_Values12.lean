import RPt_JFn_Value12_0
import RPt_JFn_Value12_1
import RPt_JFn_Value12_2
import RPt_JFn_Value12_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values12
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value12_0.value,SAQ_RecordDecode.fromRecord JFn_Value12_1.value,SAQ_RecordDecode.fromRecord JFn_Value12_2.value,SAQ_RecordDecode.fromRecord JFn_Value12_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨12,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨12,by decide⟩ _ _ _ _
    JFn_Value12_0.source JFn_Value12_1.source JFn_Value12_2.source JFn_Value12_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value12_0.value) := by
  change (1236058983<2147483647 ∧ 1842326522<2147483647 ∧ 1081455735<2147483647 ∧ 2070829967<2147483647) ∧ (431836317<2147483647 ∧ 1306907118<2147483647 ∧ 2005005026<2147483647 ∧ 1786518228<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value12_1.value) := by
  change (443387557<2147483647 ∧ 1380048824<2147483647 ∧ 1903557389<2147483647 ∧ 1021714701<2147483647) ∧ (168124661<2147483647 ∧ 1626022350<2147483647 ∧ 1551893939<2147483647 ∧ 1880490507<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value12_2.value) := by
  change (1390886039<2147483647 ∧ 701673580<2147483647 ∧ 1560804679<2147483647 ∧ 978778748<2147483647) ∧ (355003022<2147483647 ∧ 1354583439<2147483647 ∧ 688667057<2147483647 ∧ 830534546<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value12_3.value) := by
  change (594041695<2147483647 ∧ 590716042<2147483647 ∧ 1643204674<2147483647 ∧ 854254936<2147483647) ∧ (2096853037<2147483647 ∧ 1634326218<2147483647 ∧ 1235016825<2147483647 ∧ 1673069921<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 0#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value12_0.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values12
end
