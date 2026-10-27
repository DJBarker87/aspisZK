import JFn_Value17_0
import JFn_Value17_1
import JFn_Value17_2
import JFn_Value17_3
import JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values17
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value17_0.value,SAQ_RecordDecode.fromRecord JFn_Value17_1.value,SAQ_RecordDecode.fromRecord JFn_Value17_2.value,SAQ_RecordDecode.fromRecord JFn_Value17_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨17,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨17,by decide⟩ _ _ _ _
    JFn_Value17_0.source JFn_Value17_1.source JFn_Value17_2.source JFn_Value17_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value17_0.value) := by
  change (1164781923<2147483647 ∧ 5833544<2147483647 ∧ 705381050<2147483647 ∧ 2001139904<2147483647) ∧ (743439455<2147483647 ∧ 722225228<2147483647 ∧ 1231690184<2147483647 ∧ 1580115047<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value17_1.value) := by
  change (710555852<2147483647 ∧ 619358772<2147483647 ∧ 1186302413<2147483647 ∧ 802073952<2147483647) ∧ (290987046<2147483647 ∧ 1527341074<2147483647 ∧ 1784871996<2147483647 ∧ 1760991604<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value17_2.value) := by
  change (1557813380<2147483647 ∧ 800746288<2147483647 ∧ 2071554914<2147483647 ∧ 1709222532<2147483647) ∧ (1234604824<2147483647 ∧ 561330694<2147483647 ∧ 2127535449<2147483647 ∧ 785094645<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value17_3.value) := by
  change (1223599952<2147483647 ∧ 274875407<2147483647 ∧ 1758516167<2147483647 ∧ 752173464<2147483647) ∧ (1589272341<2147483647 ∧ 1766558798<2147483647 ∧ 1356246270<2147483647 ∧ 263686108<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 0#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value17_0.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values17
end
