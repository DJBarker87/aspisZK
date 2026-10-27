import RPt_JFn_Value20_0
import RPt_JFn_Value20_1
import RPt_JFn_Value20_2
import RPt_JFn_Value20_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values20
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value20_0.value,SAQ_RecordDecode.fromRecord JFn_Value20_1.value,SAQ_RecordDecode.fromRecord JFn_Value20_2.value,SAQ_RecordDecode.fromRecord JFn_Value20_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨20,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨20,by decide⟩ _ _ _ _
    JFn_Value20_0.source JFn_Value20_1.source JFn_Value20_2.source JFn_Value20_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value20_0.value) := by
  change (784635806<2147483647 ∧ 290536413<2147483647 ∧ 1913427946<2147483647 ∧ 1280508549<2147483647) ∧ (1205077619<2147483647 ∧ 2097471918<2147483647 ∧ 1333782330<2147483647 ∧ 1893294467<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value20_1.value) := by
  change (1568245334<2147483647 ∧ 1686168864<2147483647 ∧ 1119134181<2147483647 ∧ 1468476285<2147483647) ∧ (1798602319<2147483647 ∧ 127817939<2147483647 ∧ 1344162684<2147483647 ∧ 970269715<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value20_2.value) := by
  change (831430896<2147483647 ∧ 1241285235<2147483647 ∧ 1765399785<2147483647 ∧ 230690313<2147483647) ∧ (1957543568<2147483647 ∧ 369620978<2147483647 ∧ 174634496<2147483647 ∧ 1674182284<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value20_3.value) := by
  change (1388790482<2147483647 ∧ 425601028<2147483647 ∧ 930591260<2147483647 ∧ 1282365328<2147483647) ∧ (1546635047<2147483647 ∧ 1004049965<2147483647 ∧ 243105753<2147483647 ∧ 137849788<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 1#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value20_1.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values20
end
