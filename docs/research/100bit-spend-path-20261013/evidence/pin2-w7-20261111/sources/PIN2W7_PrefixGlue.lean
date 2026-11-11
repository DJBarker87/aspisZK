import PIN2_NEWGATE_verifyprefix
import PIN2W7_TranscriptCopy
import RPz7_S1SemanticCarrierV1
import RPz7_S1SemanticPrefixModelV1
/-! PIN2 W7 (2026-11-11).  Copies between the frozen preparation extraction
(`AspisR1PublicPreparation`) and the PIN2 verifier-prefix emission
(`PIN2_NEWGATE_verifyprefix`, W8, twin types, namespace `AspisR1PublicPreparationPIN2`),
and the two agreement facts the PIN2 `S1SemanticInstallation` needs:

* `parseAccepted_eq`/`parseAccepted_agree`: the PIN2 `PrefixAdapter.parseAccepted`
  (W8 Section 2, a namespace copy of ExtractedPrefixParseCore over the same
  `AspisR1PrefixAggregateParser`) is the frozen one up to the Prefix/Error copies.
* `begin_eq`/`begin_agree`: the PIN2 `r1_wire.begin` on copied inputs is the copy of
  the frozen `begin`.  Proved by unfolding both sides, which are the same text
  over copied carriers: the shared-type sampler loops are equal outright
  (`*_eq`, after `P_eq`), and `record`/`validated_record`/`sample_block_validated`/
  `semantic_validated`/`qm31_sample` and the `zc` array updates agree up to the copies
  (`*_agree`, `index_mut_map`).  The PCWN_NewLib `branch`/`from_residual` (Never) and
  the Aeneas ones (Infallible) are unfolded on concrete constructors (`w7_branch`).

Every definition below is a field-for-field copy; no Aeneas code is transcribed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PIN2W7_PrefixGlue
open AspisR1ClaimPreparedBridge (mapArray mapArray_inverse)

def rmap {A B : Type} (f : A → B) : Result A → Result B
  | ok a => ok (f a) | fail e => fail e | div => div
def cres {A A' E E' : Type} (f : A → A') (g : E → E') : core.result.Result A E → core.result.Result A' E'
  | .Ok a => .Ok (f a) | .Err e => .Err (g e)

@[simp] theorem bind_rmap {A A' B : Type} (f : A → A') (m : Result A) (k : A' → Result B) :
    (rmap f m >>= k) = (m >>= fun a => k (f a)) := by cases m <;> rfl
@[simp] theorem rmap_bind {A B C : Type} (g : B → C) (m : Result A) (k : A → Result B) :
    rmap g (m >>= k) = (m >>= fun a => rmap g (k a)) := by cases m <;> rfl
theorem bind_congr' {A B : Type} (m : Result A) (k1 k2 : A → Result B) (h : ∀ a, k1 a = k2 a) :
    (m >>= k1) = (m >>= k2) := congrArg (fun k => m >>= k) (funext h)

def error : AspisR1PublicPreparation.r1_wire.Error → AspisR1PublicPreparationPIN2.r1_wire.Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag r => .Tag r | .Length r => .Length r
  | .NonCanonical r i => .NonCanonical r i | .Boundary i => .Boundary i
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public

def pfx (p : AspisR1PublicPreparation.r1_wire.Prefix) : AspisR1PublicPreparationPIN2.r1_wire.Prefix :=
  {c1_root:=p.c1_root,records:=p.records}
def record (v : AspisR1PublicPreparation.r1_wire.ValidatedRecord) : AspisR1PublicPreparationPIN2.r1_wire.ValidatedRecord :=
  {row:=v.row,framed:=v.framed}

/-- One bind step: push the result copy under the frozen bind and match the PIN2 bind
on the same head computation (heads are defeq up to the field copies). -/
macro "w7_bind" : tactic => `(tactic| (rw [rmap_bind]; apply bind_congr'; intro _))

theorem record_agree (p : AspisR1PublicPreparation.r1_wire.Prefix) (row : U8) :
    AspisR1PublicPreparationPIN2.r1_wire.Prefix.record (pfx p) row =
      rmap (cres id error) (AspisR1PublicPreparation.r1_wire.Prefix.record p row) := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.Prefix.record AspisR1PublicPreparation.r1_wire.Prefix.record
  split
  · rfl
  · rw [rmap_bind]; apply bind_congr'; intro i
    rw [rmap_bind]; apply bind_congr'; intro s; rfl

theorem validated_record_agree (p : AspisR1PublicPreparation.r1_wire.Prefix) (row : U8) :
    AspisR1PublicPreparationPIN2.r1_wire.Prefix.validated_record (pfx p) row =
      rmap (cres record error) (AspisR1PublicPreparation.r1_wire.Prefix.validated_record p row) := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.Prefix.validated_record AspisR1PublicPreparation.r1_wire.Prefix.validated_record
  rw [record_agree, bind_rmap, rmap_bind]
  apply bind_congr'; intro r
  cases r with
  | Ok v => rfl
  | Err e => rfl

def q (x : AspisR1PublicPreparation.aspis_core.field.QM31) : AspisR1PublicPreparationPIN2.aspis_core.field.QM31 :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
def qBack (x : AspisR1PublicPreparationPIN2.aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
@[simp] theorem q_round (x : AspisR1PublicPreparation.aspis_core.field.QM31) : qBack (q x)=x := rfl
@[simp] theorem q_back (x : AspisR1PublicPreparationPIN2.aspis_core.field.QM31) : q (qBack x)=x := rfl

theorem P_eq : AspisR1PublicPreparationPIN2.aspis_core.field.P = AspisR1PublicPreparation.aspis_core.field.P := by
  unfold AspisR1PublicPreparationPIN2.aspis_core.field.P AspisR1PublicPreparation.aspis_core.field.P
  rfl
theorem div_pass_body_eq : @AspisR1PublicPreparationPIN2.sampler.qm31_div_pass_loop.body =
    @AspisR1PublicPreparation.sampler.qm31_div_pass_loop.body := by
  funext a b c
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_div_pass_loop.body AspisR1PublicPreparation.sampler.qm31_div_pass_loop.body
  rw [P_eq]
theorem div_pass_loop_eq : @AspisR1PublicPreparationPIN2.sampler.qm31_div_pass_loop =
    @AspisR1PublicPreparation.sampler.qm31_div_pass_loop := by
  funext a b c
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_div_pass_loop AspisR1PublicPreparation.sampler.qm31_div_pass_loop
  simp only [div_pass_body_eq]
theorem div_pass_eq : @AspisR1PublicPreparationPIN2.sampler.qm31_div_pass =
    @AspisR1PublicPreparation.sampler.qm31_div_pass := by
  funext a
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_div_pass AspisR1PublicPreparation.sampler.qm31_div_pass
  rw [div_pass_loop_eq]
theorem digits_body0_eq : @AspisR1PublicPreparationPIN2.sampler.qm31_digits_loop0.body =
    @AspisR1PublicPreparation.sampler.qm31_digits_loop0.body := by
  funext a b c
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_digits_loop0.body AspisR1PublicPreparation.sampler.qm31_digits_loop0.body
  rfl
theorem digits_loop0_eq : @AspisR1PublicPreparationPIN2.sampler.qm31_digits_loop0 =
    @AspisR1PublicPreparation.sampler.qm31_digits_loop0 := by
  funext a b c
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_digits_loop0 AspisR1PublicPreparation.sampler.qm31_digits_loop0
  simp only [digits_body0_eq]
theorem digits_body1_eq : @AspisR1PublicPreparationPIN2.sampler.qm31_digits_loop1.body =
    @AspisR1PublicPreparation.sampler.qm31_digits_loop1.body := by
  funext a b c
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_digits_loop1.body AspisR1PublicPreparation.sampler.qm31_digits_loop1.body
  simp only [div_pass_eq]
theorem digits_loop1_eq : @AspisR1PublicPreparationPIN2.sampler.qm31_digits_loop1 =
    @AspisR1PublicPreparation.sampler.qm31_digits_loop1 := by
  funext a b c
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_digits_loop1 AspisR1PublicPreparation.sampler.qm31_digits_loop1
  simp only [digits_body1_eq]
theorem digits_eq : @AspisR1PublicPreparationPIN2.sampler.qm31_digits =
    @AspisR1PublicPreparation.sampler.qm31_digits := by
  funext a
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_digits AspisR1PublicPreparation.sampler.qm31_digits
  rw [digits_loop0_eq, digits_loop1_eq]

theorem sample_agree (b : Array U8 32#usize) :
    AspisR1PublicPreparationPIN2.sampler.qm31_sample b =
      rmap q (AspisR1PublicPreparation.sampler.qm31_sample b) := by
  unfold AspisR1PublicPreparationPIN2.sampler.qm31_sample AspisR1PublicPreparation.sampler.qm31_sample
  rw [digits_eq, rmap_bind]; apply bind_congr'; intro d
  rw [rmap_bind]; apply bind_congr'; intro i
  rw [rmap_bind]; apply bind_congr'; intro i1
  unfold AspisR1PublicPreparationPIN2.aspis_core.field.CM31.new AspisR1PublicPreparation.aspis_core.field.CM31.new
  simp only [bind_tc_ok]
  rw [rmap_bind]; apply bind_congr'; intro i2
  rw [rmap_bind]; apply bind_congr'; intro i3
  rfl

theorem sbv_agree {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.sample_block_validated
      (PIN2W7_TranscriptCopy.digest D) (PIN2W7_TranscriptCopy.transcript t) row framed =
      rmap (fun p => (cres id error p.1, PIN2W7_TranscriptCopy.transcript p.2))
        (AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated D t row framed) := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.sample_block_validated
    AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated
  split <;> rename_i h1 <;> split <;> rename_i h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · repeat w7_bind
    rfl

/-- Result-branch and residual definitions of both libraries (PIN2 emission: PCWN_NewLib, Never;
frozen extraction: Aeneas.Std, Infallible). -/
macro "w7_branch" : tactic => `(tactic| (simp only [cres, id_eq, Aeneas.Std.uncurry,
  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
  Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
  Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
  core.convert.FromSame, bind_tc_ok, q_round]))

theorem sv_agree {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (v : AspisR1PublicPreparation.r1_wire.ValidatedRecord) :
    AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.semantic_validated
      (PIN2W7_TranscriptCopy.digest D) (PIN2W7_TranscriptCopy.transcript t) (record v) =
      rmap (fun p => (cres q error p.1, PIN2W7_TranscriptCopy.transcript p.2))
        (AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D t v) := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.semantic_validated
    AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated
  w7_bind
  split
  · rfl
  · w7_bind
    rw [sbv_agree, bind_rmap, rmap_bind]
    apply bind_congr'
    rintro ⟨r, t1⟩
    cases r with
    | Ok val =>
      w7_branch
      rw [sample_agree, bind_rmap, rmap_bind]
      apply bind_congr'; intro _; rfl
    | Err e =>
      w7_branch
      rfl

theorem index_map {A B : Type} {n : Usize} (f : A → B) (a : Std.Array A n) (i : Usize) :
    Std.Array.index_usize (mapArray f a) i = rmap f (Std.Array.index_usize a i) := by
  unfold Std.Array.index_usize
  have h : (mapArray f a)[i]? = (a[i]?).map f := by
    simp only [Std.Array.getElem?_Usize_eq, mapArray, List.getElem?_map]
  rw [h]
  cases a[i]? <;> rfl
theorem set_map {A B : Type} {n : Usize} (f : A → B) (g : B → A) (hfg : ∀ y, f (g y) = y)
    (a : Std.Array A n) (i : Usize) (y : B) :
    (mapArray f a).set i y = mapArray f (a.set i (g y)) := by
  apply Subtype.ext
  simp only [Std.Array.set, mapArray, List.map_set, hfg]
theorem repeat_map {A B : Type} (f : A → B) (n : Usize) (x : A) :
    Std.Array.repeat n (f x) = mapArray f (Std.Array.repeat n x) := by
  apply Subtype.ext
  simp only [Std.Array.repeat, mapArray, List.map_replicate]
theorem index_mut_map {A B : Type} {n : Usize} (f : A → B) (g : B → A) (hfg : ∀ y, f (g y) = y)
    (a : Std.Array A n) (i : Usize) :
    Std.Array.index_mut_usize (mapArray f a) i =
      rmap (fun p => (f p.1, fun y => mapArray f (p.2 (g y)))) (Std.Array.index_mut_usize a i) := by
  unfold Std.Array.index_mut_usize
  rw [index_map]
  cases Std.Array.index_usize a i with
  | ok x => simp only [rmap, bind_tc_ok]; congr 2; funext y; exact set_map f g hfg a i y
  | fail e => rfl
  | div => rfl

theorem ZERO_eq : AspisR1PublicPreparationPIN2.aspis_core.field.QM31.ZERO = q AspisR1PublicPreparation.aspis_core.field.QM31.ZERO := by
  unfold AspisR1PublicPreparationPIN2.aspis_core.field.QM31.ZERO AspisR1PublicPreparation.aspis_core.field.QM31.ZERO
  rfl

def challenges (c : AspisR1PublicPreparation.r1_wire.Challenges) :
    AspisR1PublicPreparationPIN2.aspis_core.state_only_prefix.r0.Challenges :=
  {lambda:=q c.lambda,chi:=q c.chi,theta:=q c.theta,zc:=mapArray q c.zc,mu:=q c.mu,eta:=q c.eta}

macro "w7_begin_step" : tactic => `(tactic| first
  | (rw [validated_record_agree, bind_rmap, rmap_bind]; apply bind_congr'; intro r; cases r <;> (try w7_branch))
  | (rw [sv_agree, bind_rmap, rmap_bind]; apply bind_congr'; rintro ⟨r, t⟩; cases r <;> (try w7_branch))
  | (rw [index_mut_map q qBack q_back, bind_rmap, rmap_bind]; apply bind_congr'; rintro ⟨x, back⟩; (try w7_branch))
  | rfl)

theorem begin_eq {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (p : AspisR1PublicPreparation.r1_wire.Prefix) (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :
    AspisR1PublicPreparationPIN2.r1_wire.begin (PIN2W7_TranscriptCopy.digest D) (pfx p) (PIN2W7_TranscriptCopy.transcript t) =
      rmap (fun x => (cres challenges error x.1, PIN2W7_TranscriptCopy.transcript x.2))
        (AspisR1PublicPreparation.r1_wire.begin D p t) := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.begin AspisR1PublicPreparation.r1_wire.begin
  simp only [ZERO_eq, repeat_map]
  repeat' w7_begin_step

/-! Reverse copies and round trips. -/
def errorBack : AspisR1PublicPreparationPIN2.r1_wire.Error → AspisR1PublicPreparation.r1_wire.Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag r => .Tag r | .Length r => .Length r
  | .NonCanonical r i => .NonCanonical r i | .Boundary i => .Boundary i
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public
@[simp] theorem error_round (e : AspisR1PublicPreparation.r1_wire.Error) : errorBack (error e)=e := by cases e <;> rfl
@[simp] theorem error_back (e : AspisR1PublicPreparationPIN2.r1_wire.Error) : error (errorBack e)=e := by cases e <;> rfl

def prefixBack (p : AspisR1PublicPreparationPIN2.r1_wire.Prefix) : AspisR1PublicPreparation.r1_wire.Prefix :=
  {c1_root:=p.c1_root,records:=p.records}
@[simp] theorem prefix_round (p : AspisR1PublicPreparation.r1_wire.Prefix) : prefixBack (pfx p)=p := rfl
@[simp] theorem prefix_back (p : AspisR1PublicPreparationPIN2.r1_wire.Prefix) : pfx (prefixBack p)=p := rfl

def transcriptBack {H : Type} (t : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H) :
    AspisR1PublicPreparation.r1_wire.SemanticTranscript H :=
  {state:=t.state,hash:=t.hash,next_row:=t.next_row}
@[simp] theorem transcript_round {H : Type} (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :
    transcriptBack (PIN2W7_TranscriptCopy.transcript t)=t := rfl
@[simp] theorem transcript_back {H : Type} (t : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H) :
    PIN2W7_TranscriptCopy.transcript (transcriptBack t)=t := rfl

def digestBack {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) :
    AspisR1PublicPreparation.aspis_core.Digest32 H :=
  {coremarkerCopyInst:=D.coremarkerCopyInst,digest:=D.digest}
@[simp] theorem digest_round {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) :
    digestBack (PIN2W7_TranscriptCopy.digest D)=D := rfl

def challengesBack (c : AspisR1PublicPreparationPIN2.aspis_core.state_only_prefix.r0.Challenges) :
    AspisR1PublicPreparation.r1_wire.Challenges :=
  {lambda:=qBack c.lambda,chi:=qBack c.chi,theta:=qBack c.theta,zc:=mapArray qBack c.zc,mu:=qBack c.mu,eta:=qBack c.eta}
@[simp] theorem challenges_round (c : AspisR1PublicPreparation.r1_wire.Challenges) : challengesBack (challenges c)=c := by
  cases c
  simp only [challengesBack, challenges, q_round, mapArray_inverse q qBack q_round]
@[simp] theorem challenges_back (c : AspisR1PublicPreparationPIN2.aspis_core.state_only_prefix.r0.Challenges) :
    challenges (challengesBack c)=c := by
  cases c
  simp only [challengesBack, challenges, q_back, mapArray_inverse qBack q q_back]

def point (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) :
    AspisR1PublicPreparationPIN2.aspis_core.circle.SecureCirclePoint := {x:=q x.x,y:=q x.y}
def pointBack (x : AspisR1PublicPreparationPIN2.aspis_core.circle.SecureCirclePoint) :
    AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint := {x:=qBack x.x,y:=qBack x.y}
@[simp] theorem point_round (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) : pointBack (point x)=x := rfl
@[simp] theorem point_back (x : AspisR1PublicPreparationPIN2.aspis_core.circle.SecureCirclePoint) : point (pointBack x)=x := rfl

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
@[simp] theorem sem_round {H : Type} (x : AspisR1PublicPreparation.r1_semantic.Verified H) : semBack (sem x)=x := by
  cases x
  simp only [semBack, sem, challenges_round, transcript_round, mapArray_inverse q qBack q_round,
    mapArray_inverse (mapArray q) (mapArray qBack) (mapArray_inverse q qBack q_round),
    mapArray_inverse point pointBack point_round]
@[simp] theorem sem_back {H : Type} (x : AspisR1PublicPreparationPIN2.r1_semantic.Verified H) : sem (semBack x)=x := by
  cases x
  simp only [semBack, sem, challenges_back, transcript_back, mapArray_inverse qBack q q_back,
    mapArray_inverse (mapArray qBack) (mapArray q) (mapArray_inverse qBack q q_back),
    mapArray_inverse pointBack point point_back]

/-- Inverse of W3c's `PreparationBinding.toPIN2` (field copy back). -/
def fromPIN2 : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public →
    AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
  | .Transfer p t => .Transfer
      { pool := p.pool, deployment_domain := p.deployment_domain,
        anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
        nullifier := p.nullifier, asset_id := p.asset_id,
        recipient_commitment := p.recipient_commitment,
        change_commitment := p.change_commitment }
      { live_snapshot :=
          { pool := t.live_snapshot.pool
            deployment_domain := t.live_snapshot.deployment_domain
            sequence := t.live_snapshot.sequence
            next_pair_index := t.live_snapshot.next_pair_index
            current_root := t.live_snapshot.current_root
            frontier := t.live_snapshot.frontier }
        candidate_afterstate :=
          { next_pair_index := t.candidate_afterstate.next_pair_index
            next_root := t.candidate_afterstate.next_root
            next_frontier := t.candidate_afterstate.next_frontier } }
  | .Withdrawal p t => .Withdrawal
      { pool := p.pool, deployment_domain := p.deployment_domain,
        anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
        nullifier := p.nullifier, asset_id := p.asset_id, amount := p.amount,
        destination_token_account := p.destination_token_account,
        change_commitment := p.change_commitment }
      { live_snapshot :=
          { pool := t.live_snapshot.pool
            deployment_domain := t.live_snapshot.deployment_domain
            sequence := t.live_snapshot.sequence
            next_pair_index := t.live_snapshot.next_pair_index
            current_root := t.live_snapshot.current_root
            frontier := t.live_snapshot.frontier }
        candidate_afterstate :=
          { next_pair_index := t.candidate_afterstate.next_pair_index
            next_root := t.candidate_afterstate.next_root
            next_frontier := t.candidate_afterstate.next_frontier } }
@[simp] theorem fromPIN2_round (p : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) :
    fromPIN2 (PreparationBinding.toPIN2 p)=p := by
  cases p <;> rfl

/-- The frozen finish model, seen through the copies as a PIN2 `VerifyPrefix.Finish`.
`S1SemanticInstallation.verify` passes `none` for the observer, and so does this adapter. -/
def finish (F : AspisR1PublicPreparation.VerifyPrefix.Finish) : AspisR1PublicPreparationPIN2.VerifyPrefix.Finish :=
  fun D p pre t ch _obs => do
    let r ← F (digestBack D) (fromPIN2 p) (prefixBack pre) (transcriptBack t) (challengesBack ch) none
    ok (match r with | .Ok v => .Ok (sem v) | .Err e => .Err (error e))

/-! Agreement facts in success form. -/
theorem parseAccepted_eq (bytes : Slice U8) :
    AspisR1PublicPreparationPIN2.PrefixAdapter.parseAccepted bytes =
      rmap (cres pfx error) (AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes) := by
  unfold AspisR1PublicPreparationPIN2.PrefixAdapter.parseAccepted AspisR1PublicPreparation.PrefixAdapter.parseAccepted
  rw [rmap_bind]; apply bind_congr'; intro r
  cases r with
  | Ok o => rfl
  | Err e => cases e <;> rfl

theorem parseAccepted_agree (bytes : Slice U8) (pre : AspisR1PublicPreparationPIN2.r1_wire.Prefix)
    (h : AspisR1PublicPreparationPIN2.PrefixAdapter.parseAccepted bytes = ok (.Ok pre)) :
    AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes = ok (.Ok (prefixBack pre)) := by
  rw [parseAccepted_eq] at h
  cases hp : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes with
  | fail e => rw [hp] at h; cases h
  | div => rw [hp] at h; cases h
  | ok r =>
    rw [hp] at h
    cases r with
    | Err e => cases h
    | Ok o =>
      have same : pfx o = pre := core.result.Result.Ok.inj (Result.ok.inj h)
      rw [← same, prefix_round]

theorem begin_agree {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparationPIN2.r1_wire.Prefix)
    (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (c : AspisR1PublicPreparationPIN2.aspis_core.state_only_prefix.r0.Challenges)
    (after : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (h : AspisR1PublicPreparationPIN2.r1_wire.begin (PIN2W7_TranscriptCopy.digest D) pre
      (PIN2W7_TranscriptCopy.transcript t) = ok (.Ok c, after)) :
    AspisR1PublicPreparation.r1_wire.begin D (prefixBack pre) t =
      ok (.Ok (challengesBack c), transcriptBack after) := by
  have eq := begin_eq D (prefixBack pre) t
  rw [prefix_back] at eq
  rw [eq] at h
  cases hb : AspisR1PublicPreparation.r1_wire.begin D (prefixBack pre) t with
  | fail e => rw [hb] at h; cases h
  | div => rw [hb] at h; cases h
  | ok r =>
    rw [hb] at h
    obtain ⟨cr, t'⟩ := r
    cases cr with
    | Err e => cases h
    | Ok c0 =>
      have hp := Result.ok.inj h
      simp only [cres, Prod.mk.injEq] at hp
      obtain ⟨hc, ht⟩ := hp
      have hc' : challenges c0 = c := core.result.Result.Ok.inj hc
      rw [← hc', ← ht, challenges_round, transcript_round]

#print axioms record_agree
#print axioms validated_record_agree
#print axioms digits_eq
#print axioms sample_agree
#print axioms sbv_agree
#print axioms sv_agree
#print axioms index_mut_map
#print axioms begin_eq
#print axioms sem_round
#print axioms sem_back
#print axioms parseAccepted_eq
#print axioms parseAccepted_agree
#print axioms begin_agree
end AspisR1PublicPreparation.PIN2W7_PrefixGlue
