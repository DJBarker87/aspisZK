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
  change (985192572<2147483647 ∧ 587313801<2147483647 ∧ 1930163796<2147483647 ∧ 614823796<2147483647) ∧ (677155461<2147483647 ∧ 1526486380<2147483647 ∧ 2128717157<2147483647 ∧ 1491212729<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value15_1.value) := by
  change (891663483<2147483647 ∧ 1927008011<2147483647 ∧ 1830133424<2147483647 ∧ 1625962134<2147483647) ∧ (1928313356<2147483647 ∧ 1154028337<2147483647 ∧ 924104527<2147483647 ∧ 426245955<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value15_2.value) := by
  change (640361814<2147483647 ∧ 1006940456<2147483647 ∧ 1290262979<2147483647 ∧ 1822248696<2147483647) ∧ (1218791108<2147483647 ∧ 1415833321<2147483647 ∧ 1423715478<2147483647 ∧ 1804611867<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value15_3.value) := by
  change (22948039<2147483647 ∧ 1623282719<2147483647 ∧ 2013917289<2147483647 ∧ 1258164445<2147483647) ∧ (1978448732<2147483647 ∧ 1162287271<2147483647 ∧ 253859989<2147483647 ∧ 239590107<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 1#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value15_1.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values15
end
