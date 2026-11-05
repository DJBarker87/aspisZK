import NHL_PreparedScalars
import NGY_Thread
import NGU_PreparedClaim
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PreparedClaim
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NFN_LPi_FieldValues NGU_Carriers NFW_PreparedControl

/-- The CLOSED NGY/NGU S8 packet is installed on the SAME produced powers.
Its semantic/compact provenance remains caller domain, not a new callee law. -/
theorem claim (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
 (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
 (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (sem : r1_semantic.Verified H)
 (semantic_finish : FinishModel.finish AspisS1ExtractedRoundChildren.children
  {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
  D pub pre beforeSemantic challenges obs=ok (.Ok sem))
 (compact before y1 : Slice U8) (compact_length : compact.val.length=464)
 (before_length : before.val.length=928)
 (compact_check : NFU_Retarget.compact.check_values compact=ok (.Ok ()))
 (expansion : NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
 (gamma inactive kappa : NE) (gamma_canonical : canonE gamma)
 (inactive_canonical : canonE inactive) (kappa_canonical : canonE kappa)
 (g : Array NE 29#usize) (same_powers : FIo_Native.weights.powers 29#usize gamma=ok g)
 (v : verifier.View) (o : Opening H) (qs : Array U32 22#usize)
 (rho : aspis_core.field.QM31) (last : transcript.Transcript H)
 (same_y1 : v.y1=y1) (same_inactive : v.inactive=NFW_PowersCohort.toPublic inactive)
 (same_kappa : o.kappa=NFW_PowersCohort.toPublic kappa) :
 ∃ out, canonE out ∧
 NGN_Cuts.claimCut NHL_PreparedScalars.actual D sem v
   (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) o qs rho last =
 ok (.Ok (PreparedScratchReachability.output sem v o.gamma o.kappa o.alpha rho qs
   (NFW_PowersCohort.toPublic out) last),
   NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) := by
 obtain ⟨out,canonical,child⟩ := NGU_PreparedClaim.packet B D pub pre beforeSemantic challenges
   obs sem semantic_finish compact before y1 compact_length before_length compact_check expansion
   gamma inactive kappa gamma_canonical inactive_canonical kappa_canonical g same_powers
 refine ⟨out,canonical,?_⟩
 unfold NGN_Cuts.claimCut
 change (do
   let r ← claimPublic D sem v.y1 v.inactive
     (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) o.kappa
   let cf ← core.result.Result.Insts.CoreOpsTry.branch r
   match cf with
   | .Continue c => ok (core.result.Result.Ok (PreparedScratchReachability.output sem v o.gamma o.kappa o.alpha rho qs c last),_)
   | .Break residual => do
     let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       verifier.Prepared (core.convert.FromSame verifier.Error) residual
     ok (r,_)) = _
 rw [same_y1,same_inactive,same_kappa,child,bind_tc_ok]
 rfl
#print axioms claim
end AspisR1.NHL_PreparedClaim
