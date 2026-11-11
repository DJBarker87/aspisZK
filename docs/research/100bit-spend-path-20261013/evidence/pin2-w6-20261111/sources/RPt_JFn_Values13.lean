import RPt_JFn_Value13_0
import RPt_JFn_Value13_1
import RPt_JFn_Value13_2
import RPt_JFn_Value13_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values13
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value13_0.value,SAQ_RecordDecode.fromRecord JFn_Value13_1.value,SAQ_RecordDecode.fromRecord JFn_Value13_2.value,SAQ_RecordDecode.fromRecord JFn_Value13_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨13,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨13,by decide⟩ _ _ _ _
    JFn_Value13_0.source JFn_Value13_1.source JFn_Value13_2.source JFn_Value13_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value13_0.value) := by
  change (459310673<2147483647 ∧ 1062300660<2147483647 ∧ 478141678<2147483647 ∧ 1800273601<2147483647) ∧ (1007693714<2147483647 ∧ 1061527668<2147483647 ∧ 2055101742<2147483647 ∧ 903733199<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value13_1.value) := by
  change (279909503<2147483647 ∧ 1958437500<2147483647 ∧ 1108142895<2147483647 ∧ 1864639497<2147483647) ∧ (146475377<2147483647 ∧ 1979421915<2147483647 ∧ 1957563416<2147483647 ∧ 989155977<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value13_2.value) := by
  change (161936727<2147483647 ∧ 490478731<2147483647 ∧ 1599415037<2147483647 ∧ 1113873558<2147483647) ∧ (1676372858<2147483647 ∧ 345853682<2147483647 ∧ 700090704<2147483647 ∧ 367805307<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value13_3.value) := by
  change (33399248<2147483647 ∧ 397764087<2147483647 ∧ 2101049919<2147483647 ∧ 408862017<2147483647) ∧ (1392796478<2147483647 ∧ 669422333<2147483647 ∧ 1389845376<2147483647 ∧ 780397513<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 1#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value13_1.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values13
end
