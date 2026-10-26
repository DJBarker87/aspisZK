import JFn_Value21_0
import JFn_Value21_1
import JFn_Value21_2
import JFn_Value21_3
import JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values21
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value21_0.value,SAQ_RecordDecode.fromRecord JFn_Value21_1.value,SAQ_RecordDecode.fromRecord JFn_Value21_2.value,SAQ_RecordDecode.fromRecord JFn_Value21_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨21,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨21,by decide⟩ _ _ _ _
    JFn_Value21_0.source JFn_Value21_1.source JFn_Value21_2.source JFn_Value21_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value21_0.value) := by
  change (1497554691<2147483647 ∧ 668726392<2147483647 ∧ 520250570<2147483647 ∧ 1887651521<2147483647) ∧ (1081528606<2147483647 ∧ 2055159448<2147483647 ∧ 1086773736<2147483647 ∧ 353720130<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value21_1.value) := by
  change (1411296291<2147483647 ∧ 1129162310<2147483647 ∧ 1767170202<2147483647 ∧ 1284306876<2147483647) ∧ (496133548<2147483647 ∧ 1977234611<2147483647 ∧ 1645476028<2147483647 ∧ 1815489495<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value21_2.value) := by
  change (441812814<2147483647 ∧ 1646979782<2147483647 ∧ 1581765854<2147483647 ∧ 1438752447<2147483647) ∧ (142547598<2147483647 ∧ 1844055308<2147483647 ∧ 2092214594<2147483647 ∧ 1236184248<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value21_3.value) := by
  change (625005061<2147483647 ∧ 370892791<2147483647 ∧ 605294985<2147483647 ∧ 1162391965<2147483647) ∧ (1065120480<2147483647 ∧ 516537978<2147483647 ∧ 1164913007<2147483647 ∧ 1025216952<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 1#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value21_1.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values21
end
