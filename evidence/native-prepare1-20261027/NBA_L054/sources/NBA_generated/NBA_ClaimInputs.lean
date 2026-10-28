import NBA_PowersCallee
import NBA_Scalars
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_ClaimInputs
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge LPi_FieldValues

theorem from_claim (x : NE) : fromClaimE (LPq_Powers.claim x)=NBA_ClaimCallee.wide x := by
  rw [←NBA_ClaimCallee.port x,from_to_e]

/-- Helper-domain contract from actual compact/expanded bytes, canonical
semantic input coordinates and the SAME producing challenge calls. Scratch
and claim are constructed; no prepare/claim/powers result is assumed. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (hs : LPq_ReadPorts.SemCanonical (toClaimSem sem))
    (compact before y1 : Slice U8) (len : compact.val.length=464) (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (expand : LPt_LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
    (start t1 t2 : transcript.Transcript H) (inactiveBytes : Slice U8)
    (gamma inactive kappa : PE)
    (gc : PreparedModel.scalar NBA_Installed.actual.sampling D start 27#u8 y1 true=ok (gamma,t1))
    (kc : PreparedModel.scalar NBA_Installed.actual.sampling D t1 28#u8 inactiveBytes false=ok (kappa,t2))
    (hi : canonE (NBA_Carriers.back inactive)) :
    ∃ (g : Array NE 29#usize) (out : NE),
      FIo_Native.weights.powers 29#usize (NBA_Carriers.back gamma)=ok g ∧
      NBA_Installed.actual.powers 29#usize gamma=ok (mapArray NBA_ClaimCallee.wide g) ∧
      LPq_PreparedTrace.Trace (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        (NBA_Carriers.back inactive) (NBA_Carriers.back kappa) out ∧ canonE out ∧
      NBA_Installed.actual.claim D sem y1 inactive (mapArray NBA_ClaimCallee.wide g) kappa=
        ok (.Ok (NBA_ClaimCallee.wide out)) := by
  have hg := (NBA_Carriers.canonical gamma).mpr (NBA_Scalars.gamma D start t1 27#u8 y1 gamma gc)
  have hk := (NBA_Carriers.canonical kappa).mpr (NBA_Scalars.ordinary D t1 t2 28#u8 inactiveBytes kappa kc)
  obtain ⟨g,native,powers,canonical⟩ := NBA_PowersCallee.source 29#usize (NBA_Carriers.back gamma) hg
  rw [NBA_Carriers.roundtrip] at powers
  have hy := LPt_ByteDomain.checked_expanded compact before y1 len size checked expand
  obtain ⟨out,tr,co,eqn⟩ := LPq_SelectedDomain.native_result (toClaimSem sem) hs y1 hy
    (XRo_Join_Carriers.arr LPq_Powers.claim g)
    (LPq_CarrierFacts.weights_from_powers _ hg g native)
    (NBA_Carriers.back inactive) (NBA_Carriers.back kappa) hi hk
  refine ⟨g,out,native,powers,tr,co,?_⟩
  rw [←NBA_Carriers.roundtrip inactive,←NBA_Carriers.roundtrip kappa,NBA_Installed.claim_slot]
  unfold claimPublic
  rw [NBA_ClaimCallee.port,NBA_ClaimCallee.port,NBA_ClaimCallee.array_port]
  have call := congrFun eqn (toClaimDigest D)
  change AspisR1CurrentPreparedClaim.verifier.prepared_claim LPm_PointLoop.ops
      (toClaimDigest D) (toClaimSem sem) y1 (LPq_Powers.claim (NBA_Carriers.back inactive))
      (XRo_Join_Carriers.arr LPq_Powers.claim g) (LPq_Powers.claim (NBA_Carriers.back kappa))=_ at call
  rw [call,bind_tc_ok]
  dsimp! only
  rw [from_claim]

#print axioms from_claim
#print axioms source
end AspisR1.NBA_ClaimInputs
end
