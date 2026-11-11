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
  change (1366453249<2147483647 ∧ 453035804<2147483647 ∧ 801156437<2147483647 ∧ 387580059<2147483647) ∧ (2094585919<2147483647 ∧ 374741513<2147483647 ∧ 1516563170<2147483647 ∧ 1779868474<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value12_1.value) := by
  change (231623459<2147483647 ∧ 950583063<2147483647 ∧ 1447714377<2147483647 ∧ 1480356504<2147483647) ∧ (1285965885<2147483647 ∧ 814346146<2147483647 ∧ 1567580457<2147483647 ∧ 1161212900<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value12_2.value) := by
  change (354930912<2147483647 ∧ 1563625920<2147483647 ∧ 2079217491<2147483647 ∧ 951969218<2147483647) ∧ (405765801<2147483647 ∧ 730058089<2147483647 ∧ 1540275453<2147483647 ∧ 1641116764<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value12_3.value) := by
  change (2044276325<2147483647 ∧ 1460634632<2147483647 ∧ 1875492885<2147483647 ∧ 889441338<2147483647) ∧ (1638191499<2147483647 ∧ 679542676<2147483647 ∧ 1044950276<2147483647 ∧ 255009955<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 3#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value12_3.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values12
end
