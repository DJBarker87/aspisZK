import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_037
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize) :
  Logged prover.MaskedFixtureAudit
  := do
  let _ ← observe .balanceAudit 0 (ok ())
  let c1_columns_inactive_balanced ← PV_L1D_Logged.lift (prover.audit_masks_loop0 c1 masks 0#usize 0#usize)
  let mask_only_columns_inactive_balanced ← PV_L1D_Logged.lift (prover.audit_masks_loop1 mask_only masks 0#usize 0#usize)
  let s ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice d))
  let q ← PV_L1D_Logged.lift (prover.inactive_sum_k s masks)
  let q1 ← PV_L1D_Logged.lift (aspis_core.field.QM31.ZERO)
  let b ← PV_L1D_Logged.lift (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q q1)
  let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice g))
  let q2 ← PV_L1D_Logged.lift (prover.inactive_sum_k s1 masks)
  let b1 ← PV_L1D_Logged.lift (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q2 q1)
  let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice h1_padding))
  let q3 ← PV_L1D_Logged.lift (prover.inactive_sum_k s2 masks)
  let b2 ← PV_L1D_Logged.lift (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q3 q1)
  Pure.pure
    {
      c1_columns_inactive_balanced,
      mask_only_columns_inactive_balanced,
      d_inactive_balanced := b,
      g_inactive_balanced := b1,
      h1_padding_inactive_balanced := b2,
      h1_total_balanced := true
    }

theorem complete_result
  (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize) :
  erase (produce c1 mask_only d g h1_padding masks) = prover.audit_masks c1 mask_only d g h1_padding masks := by
  unfold produce
  conv_rhs => unfold prover.audit_masks
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
end PV_L1D_Source_037
