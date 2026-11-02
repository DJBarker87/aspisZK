import PV_B3P_NthFormattingFinal559227
namespace PV_B3P_NextFormatting569227
open Aeneas Aeneas.Std core.ops.range PV_B3P_NthFormattingFinal559227
set_option autoImplicit false
/-- Default Range::spec_next with its entire diagnostic continuation arbitrary. -/
def source (handler : Str → Result Never) (r : Range Usize) :
    Result (Option Usize × Range Usize) :=
  if r.start.val < r.end.val then do
    let next ← PV_B3P_NthFinalGuard559227.increment_with handler r.start
    .ok (some r.start,{r with start := next})
  else .ok (none,r)

theorem binding (handler : Str → Result Never) (r : Range Usize) :
    source handler r = PV_B3Q_RangeActual.source r := by
  by_cases guard : r.start.val < r.end.val
  · have order : r.start < r.end := by scalar_tac
    simp only [source,PV_B3Q_RangeActual.source,guard,order,if_true,
      increment_value handler r.start r.end guard,bind_tc_ok]
  · have order : ¬r.start < r.end := by scalar_tac
    simp only [source,PV_B3Q_RangeActual.source,guard,order,if_false]

theorem handler_independent (first second : Str → Result Never) (r : Range Usize) :
    source first r = source second r :=
  (binding first r).trans (binding second r).symm

theorem model_binding (handler : Str → Result Never) (r : Range Usize) :
    source handler r = PV_B3Q_RangeActual.model r :=
  (binding handler r).trans (PV_B3Q_RangeActual.binding r)
#print axioms binding
#print axioms handler_independent
#print axioms model_binding
end PV_B3P_NextFormatting569227
