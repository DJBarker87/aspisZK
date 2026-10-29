import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_000
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_002
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (out : alloc.vec.Vec Std.U8) (opening : aspis_core.r0.wire.FibreOpening) :
  Logged (alloc.vec.Vec Std.U8)
  := do
  let _ ← observe .publication 0 (ok ())
  let a ← PV_L1D_Logged.lift (Array.index_usize opening.values 0#usize)
  let out1 ← PV_L1D_Logged.lift (prover.append_opening_base_row out a)
  let a1 ← PV_L1D_Logged.lift (Array.index_usize opening.values 1#usize)
  let out2 ← PV_L1D_Logged.lift (prover.append_opening_base_row out1 a1)
  let a2 ← PV_L1D_Logged.lift (Array.index_usize opening.values 2#usize)
  let out3 ← PV_L1D_Logged.lift (prover.append_opening_base_row out2 a2)
  let a3 ← PV_L1D_Logged.lift (Array.index_usize opening.values 3#usize)
  let out4 ← PV_L1D_Logged.lift (prover.append_opening_base_row out3 a3)
  let out5 ← PV_L1D_Logged.lift (prover.append_opening_secure_row out4 a)
  let out6 ← PV_L1D_Logged.lift (prover.append_opening_secure_row out5 a1)
  let out7 ← PV_L1D_Logged.lift (prover.append_opening_secure_row out6 a2)
  PV_L1D_Source_000.produce out7 a3

theorem complete_result
  (out : alloc.vec.Vec Std.U8) (opening : aspis_core.r0.wire.FibreOpening) :
  erase (produce out opening) = prover.append_opening_values out opening := by
  unfold produce
  conv_rhs => unfold prover.append_opening_values
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_000.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_000.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_000.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_002
