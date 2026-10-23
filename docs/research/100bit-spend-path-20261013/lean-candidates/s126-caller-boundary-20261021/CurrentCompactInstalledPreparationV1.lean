import CurrentCompactCallerConstantsV1
import SelectedWideViewPreparedEntryV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.InstalledPreparation
open AspisR1CurrentCaller AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open AspisR1PreparedSourcePowersBoundariesV1 AspisR1PreparedSourcePowersJointRankV1

/-- Coordinate-preserving source carriers, not a token for the public/field. -/
def retainedQ (x : aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
def retainedE (x : aspis_core.field.wide_exact.WideExact) : AspisR1PublicPreparation.aspis_core.field.WideExact := {c0:=retainedQ x.c0,c1:=retainedQ x.c1}
def retainedPoint (x : aspis_core.circle.SecureCirclePoint) : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint :=
  {x:=retainedQ x.x,y:=retainedQ x.y}
def currentQ (x : AspisR1PublicPreparation.aspis_core.field.QM31) : aspis_core.field.QM31 :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
def currentE (x : AspisR1PublicPreparation.aspis_core.field.WideExact) : aspis_core.field.wide_exact.WideExact := {c0:=currentQ x.c0,c1:=currentQ x.c1}
def currentPoint (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) : aspis_core.circle.SecureCirclePoint :=
  {x:=currentQ x.x,y:=currentQ x.y}

def retainedVariant : transport.Variant → AspisR1PublicPreparation.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def currentVariant : AspisR1PublicPreparation.transport.Variant → transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def retainedDigest {H : Type} (D : aspis_core.digest.Digest32 H) :
    AspisR1PublicPreparation.aspis_core.Digest32 H :=
  {coremarkerCopyInst:=D.coremarkerCopyInst,digest:=D.digest}

def retainedSem {H : Type} (x : r1_semantic.Verified H) :
    AspisR1PublicPreparation.r1_semantic.Verified H :=
  {roots:=x.roots,
   challenges:={
     lambda:=retainedQ x.challenges.lambda,chi:=retainedQ x.challenges.chi,
     theta:=retainedQ x.challenges.theta,zc:=mapArray retainedQ x.challenges.zc,
     mu:=retainedQ x.challenges.mu,eta:=retainedQ x.challenges.eta},
   alpha:=mapArray retainedQ x.alpha,claims:=mapArray (mapArray retainedQ) x.claims,
   extra:=mapArray retainedQ x.extra,before_z1:=mapArray retainedQ x.before_z1,
   state_before_z0:=x.state_before_z0,z:=mapArray retainedPoint x.z,
   transcript:={state:=x.transcript.state,hash:=x.transcript.hash,next_row:=x.transcript.next_row}}

def retainedView (x : verifier.View) : AspisR1PublicPreparation.verifier.View :=
  {variant:=retainedVariant x.variant,semantic:=x.semantic,y1:=x.y1,inactive:=retainedE x.inactive,
   round0:=x.round0,folded_root:=x.folded_root,round1:=x.round1,final_message:=x.final_message,
   query_bytes:=x.query_bytes}

def selectedE (x : AspisR1SelectedWideViewV1.aspis_core.field.wide_exact.WideExact) :
    aspis_core.field.wide_exact.WideExact :=
  {c0:={c0:={a:=x.c0.c0.a,b:=x.c0.c0.b},c1:={a:=x.c0.c1.a,b:=x.c0.c1.b}},
   c1:={c0:={a:=x.c1.c0.a,b:=x.c1.c0.b},c1:={a:=x.c1.c1.a,b:=x.c1.c1.b}}}

def selectedView (x : AspisR1SelectedWideViewV1.verifier.View) : verifier.View :=
  {variant:=match x.variant with | .S1 => .S1 | .S2 => .S2 | .D => .D,
   semantic:=x.semantic,y1:=x.y1,inactive:=selectedE x.inactive,round0:=x.round0,
   folded_root:=x.folded_root,round1:=x.round1,final_message:=x.final_message,query_bytes:=x.query_bytes}

def currentPrepared (x : AspisR1PublicPreparation.verifier.Prepared) : verifier.Prepared :=
  {variant:=currentVariant x.variant,roots:=x.roots,gamma:=currentE x.gamma,kappa:=currentE x.kappa,
   alpha:=mapArray currentE x.alpha,rho:=currentQ x.rho,queries:=x.queries,
   semantic_alpha:=mapArray currentQ x.semantic_alpha,z:=mapArray currentPoint x.z,
   claim:=currentE x.claim,state:=x.state}

def currentError : AspisR1PublicPreparation.verifier.Error → verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

def selectedError : AspisR1SelectedWideViewV1.verifier.Error → verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

theorem retained_selected_view (x : AspisR1SelectedWideViewV1.verifier.View) :
    retainedView (selectedView x)=AspisR1SelectedWideViewV1.preparedView x := by
  cases x with
  | mk variant semantic y1 inactive round0 folded_root round1 final_message query_bytes =>
    cases variant <;> rfl

/-- The actual selected View implementation, with full Result/error transport. -/
def sourceView (proof semantic y1 : Slice U8) :
    Result (core.result.Result verifier.View verifier.Error) := do
  let r ← AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1
  ok (match r with | .Ok v => .Ok (selectedView v) | .Err e => .Err (selectedError e))

/-- Installed retained preparation backend. All fields of its result and its
post-scratch are transported. This definition does not assert original nested
claim/fission equivalence, Rust Std/P6 correspondence or adoption. -/
def sourcePrepared (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Result ((core.result.Result verifier.Prepared verifier.Error) ×
      Array aspis_core.field.wide_exact.WideExact 29#usize) := do
  let (r,scratch) ← AspisR1PublicPreparation.PreparedScratchModel.entry
    (sourceBoundaries (installedBoundaries sampling embed)) (retainedDigest D)
    (retainedSem sem) (retainedView v) hash (mapArray retainedE g)
  ok ((match r with | .Ok out => .Ok (currentPrepared out) | .Err e => .Err (currentError e)),
    mapArray currentE scratch)

def install (ops : Ops) (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) : Ops :=
  {ConcreteConstants.withConstants ops with op5:=sourceView,op8:=sourcePrepared sampling embed}

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m;f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h

/-- Enclosing installed first proof. Its one success premise derives actual
View decoding and concrete Prepared claim/powers/joint-rank facts; neither
inactive canonicality nor the desired claim/rank equation is a premise.
SourcePrepared's explicitly documented original-source/P6 boundary remains. -/
theorem first_installed_claim_and_rank {E M Cv : Type} {L : Nat}
    (invalidAccountData : E) (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    (D : aspis_core.digest.Digest32 Unit) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : Array U8 32#usize) (length : U32)
    (error : verifier.Error → Result E) (bytes proof : Slice U8) (k : Usize)
    (out : alloc.vec.Vec U8)
    (h : FirstComposition.firstCurrent invalidAccountData (install ops sampling embed)
      D error bytes proof k=ok (.Ok out)) :
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
        ops.op9 D (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) v.semantic () none=ok (.Ok sem) ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        JointRankTrace sampling embed (retainedDigest D) p pubInput root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Tx1Reachability.afterPrepare (install ops sampling embed) D bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  obtain ⟨s,hd,hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩ :=
    FirstComposition.first_current_prepared_new invalidAccountData (install ops sampling embed)
      D error bytes proof k out h
  change sourceView proof semantic y1=ok (.Ok v) at hview
  unfold sourceView at hview
  obtain ⟨r,hr,hview⟩ := bind_success _ _ _ hview
  cases r with
  | Err e => cases hview
  | Ok oldv =>
    have hv : selectedView oldv=v := core.result.Result.Ok.inj (Result.ok.inj hview)
    subst v
    change sourcePrepared sampling embed D sem (selectedView oldv) ()
      (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) at hnew
    unfold sourcePrepared at hnew
    obtain ⟨pair,hbackend,hnew⟩ := bind_success _ _ _ hnew
    rcases pair with ⟨r,oldScratch⟩
    cases r with
    | Err e => cases hnew
    | Ok oldPrepared =>
      have heq : (core.result.Result.Ok (currentPrepared oldPrepared),mapArray currentE oldScratch)=
          (core.result.Result.Ok prepared,scratch) := Result.ok.inj hnew
      have hp : currentPrepared oldPrepared=prepared := core.result.Result.Ok.inj (congrArg Prod.fst heq)
      have hg : mapArray currentE oldScratch=scratch := congrArg Prod.snd heq
      subst prepared
      subst scratch
      rw [retained_selected_view] at hbackend
      obtain ⟨hcan,hclaim,hrank⟩ :=
        AspisR1SelectedWideViewV1.selected_view_preparation_original_payload_and_rank
          sampling embed (retainedDigest D) p pubInput root length (retainedSem sem)
          proof semantic y1 oldv () oldPrepared oldScratch
          (mapArray retainedE (Array.repeat 29#usize zero)) hr hbackend
      exact ⟨s,hd,hk,zero,semantic,y1,oldv,sem,oldPrepared,oldScratch,
        hr,hsem,hcan,hclaim,hrank,htail⟩

#print axioms retained_selected_view
#print axioms sourcePrepared
#print axioms first_installed_claim_and_rank
end AspisR1CurrentCaller.InstalledPreparation
