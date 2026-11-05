import NGU_Part008
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_PreparedClaim
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NFN_LPi_FieldValues NGU_Carriers

/-- S8 on the SAME sem/y1/inactive/g/kappa. The semantic finish and the
checked compact/expansion history are explicit producer observations. This
model theorem does not assert their native origin or the enclosing driver. -/
theorem packet (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
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
 (g : Array NE 29#usize) (same_powers : FIo_Native.weights.powers 29#usize gamma=ok g) :
 ∃ out, canonE out ∧
  claimPublic D sem y1 (NFW_PowersCohort.toPublic inactive)
   (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) (NFW_PowersCohort.toPublic kappa)=
    ok (.Ok (NFW_PowersCohort.toPublic out)) := by
 obtain ⟨out,trace,canonical,program⟩ := NGU_LPt_PreparedClaim.native_result
  B D pub pre beforeSemantic challenges obs sem semantic_finish compact before y1
  compact_length before_length compact_check expansion gamma inactive kappa
  gamma_canonical inactive_canonical kappa_canonical g same_powers
 refine ⟨out,canonical,?_⟩
 have model := congrFun program (toClaimDigest D)
 change AspisR1CurrentPreparedClaim.verifier.prepared_claim NGU_LPm_PointLoop.ops
  (toClaimDigest D) (toClaimSem sem) y1 (NGU_Powers.claim inactive)
  (arr NGU_Powers.claim g) (NGU_Powers.claim kappa)=ok (.Ok (NGU_Powers.claim out)) at model
 have maps : mapArray toClaimE (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g)=
   arr NGU_Powers.claim g := by
  apply Subtype.ext
  simp only [mapArray,NFW_PowersCohort.mapArray,arr,List.map_map]
  rfl
 unfold claimPublic
 rw [maps]
 change (do
  let r ← AspisR1CurrentPreparedClaim.verifier.prepared_claim NGU_LPm_PointLoop.ops
   (toClaimDigest D) (toClaimSem sem) y1 (NGU_Powers.claim inactive)
   (arr NGU_Powers.claim g) (NGU_Powers.claim kappa)
  ok (match r with | .Ok x => .Ok (fromClaimE x) | .Err e => .Err (fromClaimError e))) = _
 rw [model,bind_tc_ok]
 rfl

#print axioms packet
end AspisR1.NGU_PreparedClaim
end
