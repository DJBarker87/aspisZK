import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_008
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (variant : transport.Variant)
  (challenges : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
  (c1_root : Array Std.U8 32#usize) :
  Logged (core.result.Result Unit verifier.Error)
  := do
  let _ ← observe .checker 0 (ok ())
  let b ← PV_L1D_Logged.lift (core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2)
  if b
  then Pure.pure (core.result.Result.Err verifier.Error.Semantic)
  else
    let (accepted, _) ← PV_L1D_Logged.lift (aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check challenges)
    if accepted
    then Pure.pure (core.result.Result.Ok ())
    else Pure.pure (core.result.Result.Err verifier.Error.Rejected)

theorem complete_result
  (variant : transport.Variant)
  (challenges : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
  (c1_root : Array Std.U8 32#usize) :
  erase (produce variant challenges c1_root) = prover.public_check variant challenges c1_root := by
  unfold produce
  conv_rhs => unfold prover.public_check
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
end PV_L1D_Source_008
