import JFn_Value13_0
import JFn_Value13_1
import JFn_Value13_2
import JFn_Value13_3
import JFn_ArrayBuilder
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
  change (901329660<2147483647 ∧ 294142851<2147483647 ∧ 332212484<2147483647 ∧ 2141990079<2147483647) ∧ (1613711982<2147483647 ∧ 83705593<2147483647 ∧ 1349691811<2147483647 ∧ 2036132375<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value13_1.value) := by
  change (596446522<2147483647 ∧ 1330378105<2147483647 ∧ 596315588<2147483647 ∧ 1904450947<2147483647) ∧ (1031734086<2147483647 ∧ 1814216634<2147483647 ∧ 842336361<2147483647 ∧ 353269271<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value13_2.value) := by
  change (798909464<2147483647 ∧ 1890337013<2147483647 ∧ 1557033258<2147483647 ∧ 10729764<2147483647) ∧ (337453330<2147483647 ∧ 92243573<2147483647 ∧ 1926620657<2147483647 ∧ 2131245360<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value13_3.value) := by
  change (1801361440<2147483647 ∧ 957058822<2147483647 ∧ 735934588<2147483647 ∧ 150456116<2147483647) ∧ (600325266<2147483647 ∧ 1525834106<2147483647 ∧ 165589068<2147483647 ∧ 1947284288<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 0#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value13_0.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values13
end
