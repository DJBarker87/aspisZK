import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_014
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (q : Array Std.U32 22#usize) (i : Std.Usize) :
  Logged (ControlFlow Std.Usize Unit)
  := do
  let _ ← observe .queryScan 0 (ok ())
  if i < 22#usize
  then
    let i1 ← PV_L1_Logged.lift (Array.index_usize q i)
    let we ← PV_L1_Logged.lift (aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        i1)
    trace.value 5#u16 i we
    let i2 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize))
    Pure.pure (cont i2)
  else Pure.pure (done ())

theorem complete_result
  (q : Array Std.U32 22#usize) (i : Std.Usize) :
  erase (produce q i) = host_transcript.trace_queries_loop.body q i := by
  unfold produce
  conv_rhs => unfold host_transcript.trace_queries_loop.body
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_014
