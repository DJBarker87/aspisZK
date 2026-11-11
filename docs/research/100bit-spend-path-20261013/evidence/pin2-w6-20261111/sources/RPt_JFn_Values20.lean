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
  change (1238233168<2147483647 ∧ 1603811122<2147483647 ∧ 1853572471<2147483647 ∧ 1245789794<2147483647) ∧ (1566018572<2147483647 ∧ 1272771187<2147483647 ∧ 1105419423<2147483647 ∧ 51483570<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value20_1.value) := by
  change (1109489914<2147483647 ∧ 1180323456<2147483647 ∧ 959312526<2147483647 ∧ 76882658<2147483647) ∧ (326641496<2147483647 ∧ 952638474<2147483647 ∧ 67906345<2147483647 ∧ 1549785836<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value20_2.value) := by
  change (1871023420<2147483647 ∧ 1863944923<2147483647 ∧ 1149737611<2147483647 ∧ 433752140<2147483647) ∧ (156287142<2147483647 ∧ 1493438586<2147483647 ∧ 1953242572<2147483647 ∧ 2090661554<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value20_3.value) := by
  change (947355312<2147483647 ∧ 650171923<2147483647 ∧ 1823040185<2147483647 ∧ 923910460<2147483647) ∧ (1799829682<2147483647 ∧ 1850110748<2147483647 ∧ 351246619<2147483647 ∧ 462072484<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 3#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value20_3.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values20
end
