import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_046
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_047
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extras : Array aspis_core.field.QM31 29#usize) :
  Logged (alloc.vec.Vec Std.U8)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let bytes := alloc.vec.Vec.with_capacity Std.U8 3712#usize
  let a ← PV_L1D_Logged.lift (Array.index_usize claims 0#usize)
  let bytes1 ← PV_L1D_Source_046.produce bytes a
  let a1 ← PV_L1D_Logged.lift (Array.index_usize claims 1#usize)
  let bytes2 ← PV_L1D_Source_046.produce bytes1 a1
  let a2 ← PV_L1D_Logged.lift (Array.index_usize claims 2#usize)
  let bytes3 ← PV_L1D_Source_046.produce bytes2 a2
  PV_L1D_Source_046.produce bytes3 extras

theorem complete_result
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extras : Array aspis_core.field.QM31 29#usize) :
  erase (produce claims extras) = host_semantic.claim_bytes claims extras := by
  unfold produce
  conv_rhs => unfold host_semantic.claim_bytes
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_046.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_046.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_046.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_047
