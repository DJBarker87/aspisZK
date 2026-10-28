import NBA_Installed
import LPt_PreparedClaim
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_ClaimCallee
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open LPi_FieldValues

/-- Reuse the CLOSED leaf's complete eight-word carrier port. -/
abbrev wide := LPq_FieldPorts.wide

theorem port (x : NE) : toClaimE (wide x)=LPq_Powers.claim x := rfl

theorem array_port {N : Usize} (g : Array NE N) :
    mapArray toClaimE (mapArray wide g)=XRo_Join_Carriers.arr LPq_Powers.claim g := by
  apply Subtype.ext
  change (g.val.map wide).map toClaimE=g.val.map LPq_Powers.claim
  rw [List.map_map]
  rfl

/-- Full installed claim call, derived from the SAME successful semantic finish,
compact check, native expansion and native powers. No final claim is supplied. -/
theorem source (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children
      {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (compact before y1 : Slice U8) (len : compact.val.length=464)
    (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (trace : LPt_LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
    (gamma inactive kappa : NE) (hc : canonE gamma) (hi : canonE inactive) (hk : canonE kappa)
    (g : Array NE 29#usize) (powers : FIo_Native.weights.powers 29#usize gamma=ok g) :
    ∃ out, LPq_PreparedTrace.Trace (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        inactive kappa out ∧ canonE out ∧
      NBA_Installed.actual.claim D sem y1 (wide inactive) (mapArray wide g) (wide kappa)=
        ok (.Ok (fromClaimE (LPq_Powers.claim out))) ∧
      (∀ other, LPq_PreparedTrace.Trace (toClaimSem sem) y1
        (XRo_Join_Carriers.arr LPq_Powers.claim g) inactive kappa other → other=out) := by
  obtain ⟨out,tr,co,eqn⟩ := LPt_PreparedClaim.native_result B D pub pre beforeSemantic
    challenges obs sem finish compact before y1 len size checked trace
    gamma inactive kappa hc hi hk g powers
  refine ⟨out,tr,co,?_,?_⟩
  · rw [NBA_Installed.claim_slot]
    unfold claimPublic
    rw [port,port,array_port]
    have h := congrFun eqn (toClaimDigest D)
    change AspisR1CurrentPreparedClaim.verifier.prepared_claim LPm_PointLoop.ops
      (toClaimDigest D) (toClaimSem sem) y1 (LPq_Powers.claim inactive)
      (XRo_Join_Carriers.arr LPq_Powers.claim g) (LPq_Powers.claim kappa)=_ at h
    rw [h,bind_tc_ok]
  · intro other ht
    exact LPq_CarrierFacts.native_unique (toClaimDigest D) hi hk ht tr

#print axioms port
#print axioms array_port
#print axioms source
end AspisR1.NBA_ClaimCallee
end
