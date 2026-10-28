import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1_Source_012
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_013
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (blocks : Array (Array Std.U8 32#usize) 8#usize)
  (advances : Array (Array Std.U8 32#usize) 8#usize) :
  Logged (core.result.Result ((Array Std.U32 22#usize) × (Array Std.U8
    32#usize)) verifier.Error)
  := do
  let _ ← observe .queryScan 0 (ok ())
  let a := Array.repeat 22#usize 0#u32
  PV_L1_Source_012.produce blocks advances a 0#usize 0#usize

theorem complete_result
  (blocks : Array (Array Std.U8 32#usize) 8#usize)
  (advances : Array (Array Std.U8 32#usize) 8#usize) :
  erase (produce blocks advances) = host_transcript.queries_from_pairs blocks advances := by
  unfold produce
  conv_rhs => unfold host_transcript.queries_from_pairs
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_012.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_012.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_012.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_013
