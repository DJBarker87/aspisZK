import S1SemanticCarrierV1
import S1SemanticVerifyReachabilityV1
import S1SemanticRootCopyV1
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.S1SemanticInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open S1SemanticCarrier

/-- Full observed-verifier prefix and finish source bodies, on release None.
All error variants and ambient fail/div are retained through full carriers.
R/B remain explicit semantic leaves; this is not a native source adoption. -/
def verify (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) : Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error) := do
  let result ← AspisR1PublicPreparation.VerifyPrefix.verify
    (AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B))
    (retainedDigest D) (FirstComposition.toRetainedPublic pub) bytes hash none
  ok (match result with
    | .Ok sem => .Ok (currentSem sem)
    | .Err error => .Err (currentWireError error))

def install (ops : Ops) (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Ops :=
  {ops with op9:=fun {H} D pub bytes hash obs =>
    match obs with | none => verify R B D pub bytes hash | some observe => ops.op9 D pub bytes hash (some observe)}

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (success : (m >>= k)=ok out) : ∃ value,m=ok value ∧ k value=ok out := by
  cases m with
  | ok value => exact ⟨value,rfl,success⟩
  | fail error => cases success
  | div => cases success

/-- SAME semantic source return and every field, never an independent
successful prefix/finish call or a replacement semantic object. -/
theorem verify_return (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (success : verify R B D pub bytes hash=ok (.Ok sem)) :
    AspisR1PublicPreparation.VerifyPrefix.verify
      (AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B))
      (retainedDigest D) (FirstComposition.toRetainedPublic pub) bytes hash none=
        ok (.Ok (retainedSem sem)) := by
  unfold verify at success
  obtain ⟨result,source,returned⟩ := bind_success _ _ _ success
  cases result with
  | Err error => cases returned
  | Ok original =>
    have same : currentSem original=sem := core.result.Result.Ok.inj (Result.ok.inj returned)
    rw [←same,semantic_round]
    exact source

/-- Concrete semantic leaf returns source-derived roots. The parser, public
transcript, begin, finish, row payload and copy all belong to this ONE call. -/
theorem verify_roots (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (success : verify R B D pub bytes hash=ok (.Ok sem)) :
    ∃ (pre : AspisR1PublicPreparation.r1_wire.Prefix) initial after challenges
      (payload : Slice U8) (root2 : Array U8 32#usize),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      AspisR1PublicPreparation.r1_semantic.public_transcript (retainedDigest D)
        (FirstComposition.toRetainedPublic pub) hash pre.c1_root=ok (.Ok initial) ∧
      AspisR1PublicPreparation.r1_wire.begin (retainedDigest D) pre initial=ok (.Ok challenges,after) ∧
      AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B)
        (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre after challenges none=ok (.Ok (retainedSem sem)) ∧
      AspisR1PublicPreparation.FinishModel.payload pre 2#u8=ok (.Ok payload) ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload=ok (.Ok root2) ∧
      root2.val=payload.val ∧ sem.roots=Array.make 2#usize [pre.c1_root,root2] := by
  have source := verify_return R B D pub bytes hash sem success
  obtain ⟨pre,initial,after,challenges,parsed,publicInit,begin,finish⟩ :=
    AspisR1PublicPreparation.S1SemanticVerify.verify_success _ _ _ _ _ none _ source
  obtain ⟨payload,root2,hpayload,hcopy,hbytes,hroots⟩ :=
    AspisR1PublicPreparation.S1SemanticRootCopy.finish_roots R B (retainedDigest D)
      (FirstComposition.toRetainedPublic pub) pre after challenges (retainedSem sem) finish
  exact ⟨pre,initial,after,challenges,payload,root2,parsed,publicInit,begin,finish,hpayload,hcopy,hbytes,hroots⟩

#print axioms verify_return
#print axioms verify_roots
end AspisR1CurrentCaller.S1SemanticInstallation
