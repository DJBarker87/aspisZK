import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_004
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (queries : Array Std.U32 22#usize) (begin1 : Std.Usize) (end1 : Std.Usize)
  (folded : Bool) :
  Logged (alloc.vec.Vec Std.U32)
  := do
  let _ ← observe .publication 0 (ok ())
  let i ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_sub end1 begin1))
  let out := alloc.vec.Vec.with_capacity Std.U32 i
  prover.publication_indices_loop0 queries end1 folded out begin1

theorem complete_result
  (queries : Array Std.U32 22#usize) (begin1 : Std.Usize) (end1 : Std.Usize)
  (folded : Bool) :
  erase (produce queries begin1 end1 folded) = prover.publication_indices queries begin1 end1 folded := by
  unfold produce
  conv_rhs => unfold prover.publication_indices
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_004
