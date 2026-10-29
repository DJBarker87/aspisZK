import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_032
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (e : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
  Logged verifier.Error
  := do
  let _ ← observe .opening 0 (ok ())
  let b ← PV_L1D_Logged.lift (aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Insts.CoreCmpPartialEqStateOnlyMaskBuildError.eq
      e
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted)
  if b
  then Pure.pure verifier.Error.Rejected
  else Pure.pure verifier.Error.Semantic

theorem complete_result
  (e : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
  erase (produce e) = prover.mask_error e := by
  unfold produce
  conv_rhs => unfold prover.mask_error
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
end PV_L1D_Source_032
