import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_008
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
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
  let b ←
    core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2
  if b
  then ok (core.result.Result.Err verifier.Error.Semantic)
  else
    let (accepted, _) ←
      aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check challenges
    if accepted
    then ok (core.result.Result.Ok ())
    else ok (core.result.Result.Err verifier.Error.Rejected)

theorem complete_result
  (variant : transport.Variant)
  (challenges : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
  (c1_root : Array Std.U8 32#usize) :
  erase (produce variant challenges c1_root) = prover.public_check variant challenges c1_root := by
  unfold produce prover.public_check
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_008
