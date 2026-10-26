import JFn_Values10
import JFn_Values11
import JFn_Values12
import JFn_Values13
import JFn_Values14
import JFn_Values15
import JFn_Values16
import JFn_Values17
import JFn_Values18
import JFn_Values19
import JFn_Values20
import JFn_Values21
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def position (i : Fin 12) : Fin 22 := ⟨10+i.val,by have := i.isLt;omega⟩
def value (i : Fin 12) : Array SAQ_WideABI.E 4#usize := match i.val with
  | 0 => JFn_Values10.value
  | 1 => JFn_Values11.value
  | 2 => JFn_Values12.value
  | 3 => JFn_Values13.value
  | 4 => JFn_Values14.value
  | 5 => JFn_Values15.value
  | 6 => JFn_Values16.value
  | 7 => JFn_Values17.value
  | 8 => JFn_Values18.value
  | 9 => JFn_Values19.value
  | 10 => JFn_Values20.value
  | _ => JFn_Values21.value

/-- All twelve actual ordered value-array calls, on the correct closure
slice of the retained real proof. No query-acceptance premise is used. -/
theorem source (seed : Port3_NativeQueryBody.Ops) (i : Fin 12) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value (position i))=ok (value i) := by
  fin_cases i
  · exact JFn_Values10.source seed
  · exact JFn_Values11.source seed
  · exact JFn_Values12.source seed
  · exact JFn_Values13.source seed
  · exact JFn_Values14.source seed
  · exact JFn_Values15.source seed
  · exact JFn_Values16.source seed
  · exact JFn_Values17.source seed
  · exact JFn_Values18.source seed
  · exact JFn_Values19.source seed
  · exact JFn_Values20.source seed
  · exact JFn_Values21.source seed

theorem canonical (i : Fin 12) (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE ((value i).val[j.val]'(by rw [(value i).property];exact j.isLt)) := by
  fin_cases i
  · exact JFn_Values10.canonical j
  · exact JFn_Values11.canonical j
  · exact JFn_Values12.canonical j
  · exact JFn_Values13.canonical j
  · exact JFn_Values14.canonical j
  · exact JFn_Values15.canonical j
  · exact JFn_Values16.canonical j
  · exact JFn_Values17.canonical j
  · exact JFn_Values18.canonical j
  · exact JFn_Values19.canonical j
  · exact JFn_Values20.canonical j
  · exact JFn_Values21.canonical j

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values
end
