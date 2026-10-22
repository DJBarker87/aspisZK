import CurrentPreparedScratchReachability
import CallerStage2Carrier
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4PreparedNewS1AdapterV1

open AspisR1PublicPreparation
open AspisR1CurrentCaller

def qToP (q : AspisR1CurrentCaller.aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩
def qFromP (q : AspisR1PublicPreparation.aspis_core.field.QM31) : AspisR1CurrentCaller.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩
def wToP (w : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact) : AspisR1PublicPreparation.aspis_core.field.WideExact :=
  ⟨qToP w.c0, qToP w.c1⟩
def wFromP (w : AspisR1PublicPreparation.aspis_core.field.WideExact) : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact :=
  ⟨qFromP w.c0, qFromP w.c1⟩
def qArrayToP {n : Usize} (xs : Array AspisR1CurrentCaller.aspis_core.field.QM31 n) :
    Array AspisR1PublicPreparation.aspis_core.field.QM31 n := ⟨xs.val.map qToP, by simpa using xs.property⟩
def wArrayToP {n : Usize} (xs : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact n) :
    Array AspisR1PublicPreparation.aspis_core.field.WideExact n := ⟨xs.val.map wToP, by simpa using xs.property⟩
def wArrayFromP {n : Usize} (xs : Array AspisR1PublicPreparation.aspis_core.field.WideExact n) :
    Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact n := ⟨xs.val.map wFromP, by simpa using xs.property⟩

def variantToP (x : AspisR1CurrentCaller.transport.Variant) : AspisR1PublicPreparation.transport.Variant :=
  match x with | .S1 => .S1 | .S2 => .S2 | .D => .D
def semanticTranscriptToP {H : Type} (x : AspisR1CurrentCaller.r1_wire.SemanticTranscript H) :
    AspisR1PublicPreparation.r1_wire.SemanticTranscript H := ⟨x.state, x.hash, x.next_row⟩
def challengesToP (x : AspisR1CurrentCaller.aspis_core.state_only_prefix.r0.Challenges) : AspisR1PublicPreparation.r1_wire.Challenges :=
  ⟨qToP x.lambda, qToP x.chi, qToP x.theta, qArrayToP x.zc, qToP x.mu, qToP x.eta⟩
def circleToP (x : AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint) : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint :=
  ⟨qToP x.x, qToP x.y⟩
def circleArrayToP {n : Usize} (xs : Array AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint n) :
    Array AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint n :=
  ⟨xs.val.map circleToP, by simpa using xs.property⟩
def verifiedToP {H : Type} (x : AspisR1CurrentCaller.r1_semantic.Verified H) : AspisR1PublicPreparation.r1_semantic.Verified H :=
  { roots := x.roots, challenges := challengesToP x.challenges, alpha := qArrayToP x.alpha,
    claims := ⟨x.claims.val.map qArrayToP, by simp [x.claims.property]⟩,
    extra := qArrayToP x.extra, before_z1 := qArrayToP x.before_z1,
    state_before_z0 := x.state_before_z0, z := circleArrayToP x.z,
    transcript := semanticTranscriptToP x.transcript }
def viewToP (x : AspisR1CurrentCaller.verifier.View) : AspisR1PublicPreparation.verifier.View :=
  { variant := variantToP x.variant, semantic := x.semantic, y1 := x.y1,
    inactive := wToP x.inactive, round0 := x.round0, folded_root := x.folded_root,
    round1 := x.round1, final_message := x.final_message, query_bytes := x.query_bytes }
def preparedFromP (x : AspisR1PublicPreparation.verifier.Prepared) : AspisR1CurrentCaller.verifier.Prepared :=
  { variant := (match x.variant with | .S1 => .S1 | .S2 => .S2 | .D => .D),
    roots := x.roots, gamma := wFromP x.gamma, kappa := wFromP x.kappa,
    alpha := wArrayFromP x.alpha, rho := qFromP x.rho, queries := x.queries,
    semantic_alpha := ⟨x.semantic_alpha.val.map qFromP, by simpa using x.semantic_alpha.property⟩,
    z := ⟨x.z.val.map (fun z => (⟨qFromP z.x, qFromP z.y⟩ : AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint)),
          by simpa using x.z.property⟩,
    claim := wFromP x.claim, state := x.state }
def errorFromP (x : AspisR1PublicPreparation.verifier.Error) : AspisR1CurrentCaller.verifier.Error :=
  match x with
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def currentDigestToP {H : Type} (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) : AspisR1PublicPreparation.aspis_core.Digest32 H :=
  ⟨d.coremarkerCopyInst, d.digest⟩

def mappedPreparedInner (r : core.result.Result AspisR1PublicPreparation.verifier.Prepared AspisR1PublicPreparation.verifier.Error) :
    core.result.Result AspisR1CurrentCaller.verifier.Prepared AspisR1CurrentCaller.verifier.Error :=
  match r with
  | .Ok p => .Ok (preparedFromP p)
  | .Err e => .Err (errorFromP e)

def prepareByS1Body (B : AspisR1PublicPreparation.PreparedScratchModel.Boundaries) {H : Type}
    (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (v : AspisR1CurrentCaller.verifier.View) (hash : H)
    (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    Result ((core.result.Result AspisR1CurrentCaller.verifier.Prepared AspisR1CurrentCaller.verifier.Error) ×
      Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) := do
  let (inner, scratch) ← AspisR1PublicPreparation.PreparedScratchModel.prepare B (currentDigestToP d)
    (verifiedToP sem) (viewToP v) hash (wArrayToP g)
  pure (mappedPreparedInner inner, wArrayFromP scratch)

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The mapped exact emitted Prepared body preserves the powers call and caller-owned
scratch as one same-run fact. Child operations are the explicit S1 boundary bundle B. -/
theorem prepareByS1Body_success_powers {H : Type}
    (B : AspisR1PublicPreparation.PreparedScratchModel.Boundaries) (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H) (v : AspisR1CurrentCaller.verifier.View) (hash : H)
    (out : AspisR1CurrentCaller.verifier.Prepared)
    (scratchIn scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (h : prepareByS1Body B d sem v hash scratchIn = .ok (.Ok out, scratch)) :
    ∃ (gamma : AspisR1PublicPreparation.aspis_core.field.WideExact) (powers : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      out.gamma = wFromP gamma ∧ B.powers 29#usize gamma = .ok powers ∧
      wArrayFromP powers = scratch := by
  unfold prepareByS1Body at h
  obtain ⟨pair, hmodel, hmap⟩ := bind_success _ _ _ h
  rcases pair with ⟨inner, scratchP⟩
  have hpair : (mappedPreparedInner inner, wArrayFromP scratchP) = (.Ok out, scratch) := by
    change Result.ok (mappedPreparedInner inner, wArrayFromP scratchP) = Result.ok (.Ok out, scratch) at hmap
    exact Result.ok.inj hmap
  have hinner : mappedPreparedInner inner = .Ok out := hpair.1
  have hscratch : wArrayFromP scratchP = scratch := hpair.2
  cases inner with
  | Err e => simp [mappedPreparedInner] at hinner
  | Ok p =>
    have hp : preparedFromP p = out := by simpa [mappedPreparedInner] using hinner
    have hmodel' : AspisR1PublicPreparation.PreparedScratchModel.prepare B (currentDigestToP d)
          (verifiedToP sem) (viewToP v) hash (wArrayToP scratchIn) = .ok (.Ok p, scratchP) := by
        simpa using hmodel
    obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hgamma,hbytes,hkappa,
      halpha0,tail⟩ := AspisR1PublicPreparation.PreparedScratchReachability.prepare_success B (currentDigestToP d)
        (verifiedToP sem) (viewToP v) hash p scratchP (wArrayToP scratchIn) hmodel'
    have hgam : p.gamma = gamma := by
      cases tail with
      | single hfolds tail =>
        rcases tail with ⟨queries,after,last,rho,claim,hq,hr,hpowers,hclaim,hout⟩
        have hh := congrArg (fun z : AspisR1PublicPreparation.verifier.Prepared => z.gamma) hout
        simpa [AspisR1PublicPreparation.PreparedScratchReachability.output] using hh
      | double hfolds root b1 b2 alpha1 afterAlpha hroot hb1 hb2 halpha tail =>
        rcases tail with ⟨queries,after,last,rho,claim,hq,hr,hpowers,hclaim,hout⟩
        have hh := congrArg (fun z : AspisR1PublicPreparation.verifier.Prepared => z.gamma) hout
        simpa [AspisR1PublicPreparation.PreparedScratchReachability.output] using hh
    have houtg : out.gamma = wFromP gamma := by
      have hh := congrArg (fun z : AspisR1CurrentCaller.verifier.Prepared => z.gamma) hp
      simpa [preparedFromP, hgam] using hh.symm
    have hpowers : B.powers 29#usize gamma = .ok pair.2 := by
      cases tail with
      | single _ ht => rcases ht with ⟨_,_,_,_,_,_,_,hp,_,_⟩; exact hp
      | double _ _ _ _ _ _ _ _ _ _ ht => rcases ht with ⟨_,_,_,_,_,_,_,hp,_,_⟩; exact hp
    exact ⟨gamma, scratchP, houtg, hpowers, hscratch⟩

end AspisR1S4PreparedNewS1AdapterV1
