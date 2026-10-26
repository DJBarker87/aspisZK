import RPz7_CurrentPreparedClaimCarriers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim

def toClaimChallenges (x : AspisR1PublicPreparation.r1_wire.Challenges) :
    r1_wire.Challenges :=
  {lambda:=toClaimQ x.lambda,chi:=toClaimQ x.chi,theta:=toClaimQ x.theta,
   zc:=mapArray toClaimQ x.zc,mu:=toClaimQ x.mu,eta:=toClaimQ x.eta}
def toClaimPoint (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) :
    aspis_core.circle.SecureCirclePoint := {x:=toClaimQ x.x,y:=toClaimQ x.y}
def toClaimSem {H : Type} (x : AspisR1PublicPreparation.r1_semantic.Verified H) :
    r1_semantic.Verified H :=
  {roots:=x.roots,challenges:=toClaimChallenges x.challenges,
   alpha:=mapArray toClaimQ x.alpha,claims:=mapArray (mapArray toClaimQ) x.claims,
   extra:=mapArray toClaimQ x.extra,before_z1:=mapArray toClaimQ x.before_z1,
   state_before_z0:=x.state_before_z0,z:=mapArray toClaimPoint x.z,
   transcript:={state:=x.transcript.state,hash:=x.transcript.hash,next_row:=x.transcript.next_row}}
def toClaimDigest {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) :
    aspis_core.Digest32 H := {coremarkerCopyInst:=D.coremarkerCopyInst,digest:=D.digest}
def fromClaimError (e : verifier.Error) : AspisR1PublicPreparation.verifier.Error :=
  match e with
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

local notation "QRaw" => AspisR1EbyKPushDecodedProductUpdate.QRaw

def powersPublic (N : Usize) (x : PE) : Result (Array PE N) := do
  let ys ← ClaimPowers.powers N (toClaimE x)
  ok (mapArray fromClaimE ys)
def claimPublic {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE) :
    Result (core.result.Result PE AspisR1PublicPreparation.verifier.Error) := do
  let r ← verifier.prepared_claim (AspisR1S5ClaimDotConcreteAdapter.concreteOps QRaw)
    (toClaimDigest D) (toClaimSem sem) y1 (toClaimE inactive) (mapArray toClaimE g) (toClaimE kappa)
  ok (match r with
    | .Ok x => .Ok (fromClaimE x)
    | .Err e => .Err (fromClaimError e))
def concreteBoundaries (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    AspisR1PublicPreparation.PreparedScratchModel.Boundaries :=
  {sampling:=sampling,powers:=powersPublic,claim:=claimPublic}

theorem powersPublic_success {N : Usize} (x : PE) (out : Array PE N)
    (h : powersPublic N x=ok out) :
    ClaimPowers.powers N (toClaimE x)=ok (mapArray toClaimE out) := by
  unfold powersPublic at h
  cases hr : ClaimPowers.powers N (toClaimE x) with
  | fail e => simp only [hr,bind_tc_fail] at h; cases h
  | div => simp only [hr,bind_tc_div] at h; cases h
  | ok ys =>
    simp only [hr,bind_tc_ok] at h
    have he := Result.ok.inj h
    rw [← he,to_from_array]

theorem claimPublic_success {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive kappa out : PE) (g : Array PE 29#usize)
    (h : claimPublic D sem y1 inactive g kappa=ok (.Ok out)) :
    verifier.prepared_claim (AspisR1S5ClaimDotConcreteAdapter.concreteOps QRaw)
      (toClaimDigest D) (toClaimSem sem) y1 (toClaimE inactive) (mapArray toClaimE g) (toClaimE kappa)=
      ok (.Ok (toClaimE out)) := by
  unfold claimPublic at h
  cases hr : verifier.prepared_claim (AspisR1S5ClaimDotConcreteAdapter.concreteOps QRaw)
      (toClaimDigest D) (toClaimSem sem) y1 (toClaimE inactive) (mapArray toClaimE g) (toClaimE kappa) with
  | fail e => simp only [hr,bind_tc_fail] at h; cases h
  | div => simp only [hr,bind_tc_div] at h; cases h
  | ok r =>
    cases r with
    | Err e => simp only [hr,bind_tc_ok] at h; cases h
    | Ok x =>
      simp only [hr,bind_tc_ok] at h
      have he := core.result.Result.Ok.inj (Result.ok.inj h)
      rw [← he,to_from_e]

#print axioms powersPublic_success
#print axioms claimPublic_success
end AspisR1ClaimPreparedBridge
