import PIN2_VERIFYPREFIX_EMISSION -- PLACEHOLDER: the PIN2 translator emission of the verifier prefix
import PIN2W7_TranscriptCopy
import RPz7_S1SemanticCarrierV1
/-! PIN2 W7 DRAFT (2026-11-11), not compiled.  Carrier copies between the
frozen preparation extraction (`AspisR1PublicPreparation`) and a fresh PIN2
translator emission of the verifier prefix (`AspisR1PublicPreparationPIN2`),
in the pattern of the release `InstalledPreparation.{currentQ,retainedQ,...}`
and `S1SemanticCarrier.{currentSem,semantic_round,...}` (which copy between
the preparation and current-caller extractions).  Every definition here is a
field-for-field copy; nothing is transcribed from Aspis code.

Assumed emission names (adjust when it lands; the existing PIN2 emissions use
the new naming): `aspis_core.digest.Digest32`, `aspis_core.field.QM31`
(`c0 c1 : CM31`, `CM31 = {a b}`), `aspis_core.circle.SecureCirclePoint`
(`x y : QM31`), `r1_wire.{Prefix,Challenges,SemanticTranscript,Error}`,
`r1_semantic.Verified`, `pool_v1.pair_forest_semantic_terminal.r0.Public`.

Two facts are NOT copies and must come from the emission plus the
fresh-equals-gate comparison (the functions are unchanged at PIN2 per
PIN2_FUNCTION_DIFF): `parseAccepted_agree` and `begin_agree`.  Their bodies
are marked `pin2_pending_emission` (an undefined tactic, so this file cannot
compile by accident).  If the translator instead emits the PIN2 prefix over
the frozen types (types unchanged at PIN2), this whole module except
`PIN2W7_TranscriptCopy` becomes unnecessary. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PIN2W7_PrefixGlue
open AspisR1ClaimPreparedBridge (mapArray mapArray_inverse)

abbrev P2 := AspisR1PublicPreparationPIN2

def q (x : AspisR1PublicPreparation.aspis_core.field.QM31) : AspisR1PublicPreparationPIN2.aspis_core.field.QM31 :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
def qBack (x : AspisR1PublicPreparationPIN2.aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
@[simp] theorem q_round (x) : qBack (q x)=x := rfl
@[simp] theorem q_back (x) : q (qBack x)=x := rfl

def point (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) :
    AspisR1PublicPreparationPIN2.aspis_core.circle.SecureCirclePoint := {x:=q x.x,y:=q x.y}
def pointBack (x : AspisR1PublicPreparationPIN2.aspis_core.circle.SecureCirclePoint) :
    AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint := {x:=qBack x.x,y:=qBack x.y}
@[simp] theorem point_round (x) : pointBack (point x)=x := rfl
@[simp] theorem point_back (x) : point (pointBack x)=x := rfl

def digestBack {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) :
    AspisR1PublicPreparation.aspis_core.Digest32 H :=
  {coremarkerCopyInst:=D.coremarkerCopyInst,digest:=D.digest}
@[simp] theorem digest_round {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) :
    digestBack (PIN2W7_TranscriptCopy.digest D)=D := rfl

def transcriptBack {H : Type} (t : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H) :
    AspisR1PublicPreparation.r1_wire.SemanticTranscript H :=
  {state:=t.state,hash:=t.hash,next_row:=t.next_row}
@[simp] theorem transcript_round {H : Type} (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :
    transcriptBack (PIN2W7_TranscriptCopy.transcript t)=t := rfl
@[simp] theorem transcript_back {H : Type} (t : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H) :
    PIN2W7_TranscriptCopy.transcript (transcriptBack t)=t := rfl

def prefix (p : AspisR1PublicPreparation.r1_wire.Prefix) : AspisR1PublicPreparationPIN2.r1_wire.Prefix :=
  {c1_root:=p.c1_root,records:=p.records}
def prefixBack (p : AspisR1PublicPreparationPIN2.r1_wire.Prefix) : AspisR1PublicPreparation.r1_wire.Prefix :=
  {c1_root:=p.c1_root,records:=p.records}
@[simp] theorem prefix_round (p) : prefixBack (prefix p)=p := rfl
@[simp] theorem prefix_back (p) : prefix (prefixBack p)=p := rfl

def challenges (c : AspisR1PublicPreparation.r1_wire.Challenges) : AspisR1PublicPreparationPIN2.r1_wire.Challenges :=
  {lambda:=q c.lambda,chi:=q c.chi,theta:=q c.theta,zc:=mapArray q c.zc,mu:=q c.mu,eta:=q c.eta}
def challengesBack (c : AspisR1PublicPreparationPIN2.r1_wire.Challenges) : AspisR1PublicPreparation.r1_wire.Challenges :=
  {lambda:=qBack c.lambda,chi:=qBack c.chi,theta:=qBack c.theta,zc:=mapArray qBack c.zc,mu:=qBack c.mu,eta:=qBack c.eta}

def sem {H : Type} (x : AspisR1PublicPreparation.r1_semantic.Verified H) : AspisR1PublicPreparationPIN2.r1_semantic.Verified H :=
  {roots:=x.roots,challenges:=challenges x.challenges,
   alpha:=mapArray q x.alpha,claims:=mapArray (mapArray q) x.claims,
   extra:=mapArray q x.extra,before_z1:=mapArray q x.before_z1,
   state_before_z0:=x.state_before_z0,z:=mapArray point x.z,
   transcript:=PIN2W7_TranscriptCopy.transcript x.transcript}
def semBack {H : Type} (x : AspisR1PublicPreparationPIN2.r1_semantic.Verified H) : AspisR1PublicPreparation.r1_semantic.Verified H :=
  {roots:=x.roots,challenges:=challengesBack x.challenges,
   alpha:=mapArray qBack x.alpha,claims:=mapArray (mapArray qBack) x.claims,
   extra:=mapArray qBack x.extra,before_z1:=mapArray qBack x.before_z1,
   state_before_z0:=x.state_before_z0,z:=mapArray pointBack x.z,
   transcript:=transcriptBack x.transcript}
@[simp] theorem sem_round {H : Type} (x : AspisR1PublicPreparation.r1_semantic.Verified H) :
    semBack (sem x)=x := by
  cases x with
  | mk roots ch alpha claims extra before state z transcript =>
    cases ch
    cases transcript
    simp only [semBack,sem,challengesBack,challenges,transcriptBack,PIN2W7_TranscriptCopy.transcript,q_round,
      mapArray_inverse q qBack q_round,
      mapArray_inverse (mapArray q) (mapArray qBack) (mapArray_inverse q qBack q_round),
      mapArray_inverse point pointBack point_round]
@[simp] theorem sem_back {H : Type} (x : AspisR1PublicPreparationPIN2.r1_semantic.Verified H) :
    sem (semBack x)=x := by
  cases x with
  | mk roots ch alpha claims extra before state z transcript =>
    cases ch
    cases transcript
    simp only [semBack,sem,challengesBack,challenges,transcriptBack,PIN2W7_TranscriptCopy.transcript,q_back,
      mapArray_inverse qBack q q_back,
      mapArray_inverse (mapArray qBack) (mapArray q) (mapArray_inverse qBack q q_back),
      mapArray_inverse pointBack point point_back]

def error : AspisR1PublicPreparation.r1_wire.Error → AspisR1PublicPreparationPIN2.r1_wire.Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag r => .Tag r | .Length r => .Length r
  | .NonCanonical r i => .NonCanonical r i | .Boundary i => .Boundary i
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public
def errorBack : AspisR1PublicPreparationPIN2.r1_wire.Error → AspisR1PublicPreparation.r1_wire.Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag r => .Tag r | .Length r => .Length r
  | .NonCanonical r i => .NonCanonical r i | .Boundary i => .Boundary i
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public
@[simp] theorem error_round (e) : errorBack (error e)=e := by cases e <;> rfl
@[simp] theorem error_back (e) : error (errorBack e)=e := by cases e <;> rfl

/-- Inverse of W3c's `PreparationBinding.toPIN2` (field copy back). -/
def fromPIN2 : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public →
    AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
  | .Transfer p t => .Transfer
      {pool:=p.pool,deployment_domain:=p.deployment_domain,anchor_sequence:=p.anchor_sequence,
       anchor_root:=p.anchor_root,nullifier:=p.nullifier,asset_id:=p.asset_id,
       recipient_commitment:=p.recipient_commitment,change_commitment:=p.change_commitment}
      {live_snapshot:={pool:=t.live_snapshot.pool,deployment_domain:=t.live_snapshot.deployment_domain,
         sequence:=t.live_snapshot.sequence,next_pair_index:=t.live_snapshot.next_pair_index,
         current_root:=t.live_snapshot.current_root,frontier:=t.live_snapshot.frontier},
       candidate_afterstate:={next_pair_index:=t.candidate_afterstate.next_pair_index,
         next_root:=t.candidate_afterstate.next_root,next_frontier:=t.candidate_afterstate.next_frontier}}
  | .Withdrawal p t => .Withdrawal
      {pool:=p.pool,deployment_domain:=p.deployment_domain,anchor_sequence:=p.anchor_sequence,
       anchor_root:=p.anchor_root,nullifier:=p.nullifier,asset_id:=p.asset_id,amount:=p.amount,
       destination_token_account:=p.destination_token_account,change_commitment:=p.change_commitment}
      {live_snapshot:={pool:=t.live_snapshot.pool,deployment_domain:=t.live_snapshot.deployment_domain,
         sequence:=t.live_snapshot.sequence,next_pair_index:=t.live_snapshot.next_pair_index,
         current_root:=t.live_snapshot.current_root,frontier:=t.live_snapshot.frontier},
       candidate_afterstate:={next_pair_index:=t.candidate_afterstate.next_pair_index,
         next_root:=t.candidate_afterstate.next_root,next_frontier:=t.candidate_afterstate.next_frontier}}
@[simp] theorem fromPIN2_round (p) : fromPIN2 (PreparationBinding.toPIN2 p)=p := by
  cases p <;> rfl

/-- The frozen finish model, seen through the copies as a PIN2 `VerifyPrefix.Finish`.
The `obs` argument is passed only as `none` by `S1SemanticInstallation.verify`;
`obsBack` maps the emission's phase observer to the frozen one (PENDING: the
emission's phase type; `none ↦ none` is all the installation needs). -/
def finish (F : AspisR1PublicPreparation.VerifyPrefix.Finish) : AspisR1PublicPreparationPIN2.VerifyPrefix.Finish :=
  fun D p pre t ch _obs => do
    let r ← F (digestBack D) (fromPIN2 p) (prefixBack pre) (transcriptBack t) (challengesBack ch) none
    ok (match r with | .Ok v => .Ok (sem v) | .Err e => .Err (error e))

/-- PENDING EMISSION (fresh-equals-gate): the PIN2 prefix parser is the frozen one up to the copy. -/
theorem parseAccepted_agree (bytes : Slice U8) (pre : AspisR1PublicPreparationPIN2.r1_wire.Prefix)
    (h : AspisR1PublicPreparationPIN2.PrefixAdapter.parseAccepted bytes = ok (.Ok pre)) :
    AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes = ok (.Ok (prefixBack pre)) := by
  pin2_pending_emission

/-- PENDING EMISSION (fresh-equals-gate): `r1_wire.begin` is the frozen one up to the copies. -/
theorem begin_agree {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparationPIN2.r1_wire.Prefix)
    (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (c : AspisR1PublicPreparationPIN2.r1_wire.Challenges)
    (after : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (h : AspisR1PublicPreparationPIN2.r1_wire.begin (PIN2W7_TranscriptCopy.digest D) pre
      (PIN2W7_TranscriptCopy.transcript t) = ok (.Ok c, after)) :
    AspisR1PublicPreparation.r1_wire.begin D (prefixBack pre) t = ok (.Ok (challengesBack c), transcriptBack after) := by
  pin2_pending_emission

end AspisR1PublicPreparation.PIN2W7_PrefixGlue
