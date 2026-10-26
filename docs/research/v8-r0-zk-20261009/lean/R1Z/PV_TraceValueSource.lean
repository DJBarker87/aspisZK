import R1Z.PV_CurrentDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_TraceValueSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev aspis_core.field.wide_exact.WideExact := ProverRwFull.aspis_core.field.wide_exact.WideExact
/-- [aspis_r1_cost_probe::trace::value]:
    Source: 'crates/aspis-r1-cost-probe/src/trace.rs', lines 6:0-11:1
    Visibility: public -/
def trace.value
  (tag : Std.U16) (index : Std.Usize)
  (x : aspis_core.field.wide_exact.WideExact) :
  Result Unit
  := do
  ok ()

theorem exact (tag : U16) (index : Usize) (x : aspis_core.field.wide_exact.WideExact) :
    trace.value tag index x = ok () := rfl
theorem operands_erased (tag tag' : U16) (index index' : Usize)
    (x y : aspis_core.field.wide_exact.WideExact) :
    trace.value tag index x = trace.value tag' index' y := rfl
#print axioms exact
#print axioms operands_erased
end R1Z.PV_TraceValueSource
