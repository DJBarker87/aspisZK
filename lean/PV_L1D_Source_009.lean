import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_009
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (word : Slice aspis_core.field.wide_exact.WideExact)
  (salts : host_commitment.PrivateSalts) :
  Logged (alloc.vec.Vec (Array Std.U8 32#usize))
  := do
  let _ ← observe .opening 0 (ok ())
  let i ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_shl 1#usize 18#u32))
  let leaves := alloc.vec.Vec.with_capacity (Array Std.U8 32#usize) i
  prover.folded_leaves_loop0 hash word salts leaves 0#usize

theorem complete_result
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (word : Slice aspis_core.field.wide_exact.WideExact)
  (salts : host_commitment.PrivateSalts) :
  erase (produce hash word salts) = prover.folded_leaves hash word salts := by
  unfold produce
  conv_rhs => unfold prover.folded_leaves
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
end PV_L1D_Source_009
