import RPt_JFn_Value11_0
import RPt_JFn_Value11_1
import RPt_JFn_Value11_2
import RPt_JFn_Value11_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values11
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value11_0.value,SAQ_RecordDecode.fromRecord JFn_Value11_1.value,SAQ_RecordDecode.fromRecord JFn_Value11_2.value,SAQ_RecordDecode.fromRecord JFn_Value11_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨11,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨11,by decide⟩ _ _ _ _
    JFn_Value11_0.source JFn_Value11_1.source JFn_Value11_2.source JFn_Value11_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value11_0.value) := by
  change (939634098<2147483647 ∧ 31431390<2147483647 ∧ 696747450<2147483647 ∧ 309953685<2147483647) ∧ (1224205441<2147483647 ∧ 619654007<2147483647 ∧ 1209377263<2147483647 ∧ 1914339141<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value11_1.value) := by
  change (2096783160<2147483647 ∧ 973349216<2147483647 ∧ 58875228<2147483647 ∧ 883428442<2147483647) ∧ (1992183950<2147483647 ∧ 1411562134<2147483647 ∧ 1199675175<2147483647 ∧ 925513126<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value11_2.value) := by
  change (12674944<2147483647 ∧ 1246410058<2147483647 ∧ 116774269<2147483647 ∧ 918536601<2147483647) ∧ (1000197073<2147483647 ∧ 68609528<2147483647 ∧ 19935596<2147483647 ∧ 1874953030<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value11_3.value) := by
  change (2113538273<2147483647 ∧ 472258602<2147483647 ∧ 1891916025<2147483647 ∧ 1511907743<2147483647) ∧ (300398393<2147483647 ∧ 1245637887<2147483647 ∧ 1073497836<2147483647 ∧ 2094029351<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 2#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value11_2.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values11
end
