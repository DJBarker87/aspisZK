import RPt_JFn_Value19_0
import RPt_JFn_Value19_1
import RPt_JFn_Value19_2
import RPt_JFn_Value19_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values19
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value19_0.value,SAQ_RecordDecode.fromRecord JFn_Value19_1.value,SAQ_RecordDecode.fromRecord JFn_Value19_2.value,SAQ_RecordDecode.fromRecord JFn_Value19_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨19,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨19,by decide⟩ _ _ _ _
    JFn_Value19_0.source JFn_Value19_1.source JFn_Value19_2.source JFn_Value19_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value19_0.value) := by
  change (383528936<2147483647 ∧ 1420741281<2147483647 ∧ 1451227438<2147483647 ∧ 858158777<2147483647) ∧ (1122667547<2147483647 ∧ 1367258078<2147483647 ∧ 969245844<2147483647 ∧ 2070711175<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value19_1.value) := by
  change (679627658<2147483647 ∧ 122729708<2147483647 ∧ 2082012209<2147483647 ∧ 1591486637<2147483647) ∧ (228287470<2147483647 ∧ 990747238<2147483647 ∧ 1374281538<2147483647 ∧ 18953776<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value19_2.value) := by
  change (57344183<2147483647 ∧ 583388825<2147483647 ∧ 1085430026<2147483647 ∧ 963775737<2147483647) ∧ (70571030<2147483647 ∧ 1774603832<2147483647 ∧ 221175620<2147483647 ∧ 387274823<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value19_3.value) := by
  change (85454462<2147483647 ∧ 924745290<2147483647 ∧ 1242669385<2147483647 ∧ 39751405<2147483647) ∧ (392368867<2147483647 ∧ 155221954<2147483647 ∧ 448471766<2147483647 ∧ 636734932<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 3#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value19_3.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values19
end
