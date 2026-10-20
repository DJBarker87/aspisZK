import RecordedBinaryExperimentBin
import RawLiteralDecoderRestore
import RawFullPublicRun

set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireInitialTag
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open CanonicalAddressEmbedding

/-- Follow only returns values in the range of its pure output function. -/
theorem follow_range {I A X C : Type} [DecidableEq I] [Inhabited A]
    (g : X → List A → C) (tr : List (I × A)) (own : BS I A X)
    (pend : List (I × Option A)) (T : Table I A) (out : C)
    (h : bfollow g tr own pend T = some out) : ∃ x extra, g x extra = out := by
  have fin (s : BS I A X) (ps : List (I × Option A))
      (h : finished g s ps = some out) : ∃ x extra, g x extra = out := by
    cases s with
    | ask i k => cases h
    | spawn i k => cases h
    | done x =>
      simp only [finished] at h
      split at h
      · exact ⟨x, answers ps, Option.some.inj h⟩
      · cases h
  induction tr generalizing own pend T with
  | nil => exact fin _ _ h
  | cons q rest ih =>
    simp only [bfollow] at h
    split at h
    · rename_i c he
      exact fin _ _ (he.trans h)
    · split at h
      · split at h
        · cases h
        · split at h
          · exact ih _ _ _ h
          · cases h
      · split at h
        · split at h
          · exact ih _ _ _ h
          · cases h
        · exact ih _ _ _ h

theorem raw_pointwise (pub : LiteralTranscript.Public) (a : AddrC SelectedTranscriptParams.L)
    (T : Table Bytes State) (own : BS Bytes State (List State))
    (pend : List (Bytes × Option State))
    (g : List State → List State → RawLiteralDecoderDensity.Output)
    (hd : RawUnifiedDecoder.decode SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub
      (toBytes a) T = some (own,pend,g))
    (hp : PublicInitParse.parse pub.pubBytes a.val = some
      ((PublicInitParse.parse pub.pubBytes a.val).getD default)) :
    ∀ x extra, (g x extra).1.statement = pub := by
  rw [RawUnifiedDecoder.decode_of_canonical] at hd
  unfold RawUnifiedDecoder.atCanonical at hd
  split at hd
  · cases hd
  · rename_i bs ps bg hb
    have hi := UnifiedDecoder.decode_of_init_parse SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a.val
      (RawBoundedTrace.table SelectedTranscriptParams.L T) _ hp
    rw [hi, UnifiedDecoder.component_initial] at hb
    obtain ⟨bs0,ps0,g0,h0,he⟩ := DecoderStateList.lift_sound _ _ _ _ _ _ hb
    obtain ⟨root, hparse, htuple⟩ := UnifiedInitialDecoder.decode_sound _ _ _ _ _ _ _ _ h0
    cases htuple
    cases he
    cases hd
    intro x extra
    rfl

/-- The initial public selector fixes tag 2, independently of the supplied tag. -/
theorem initial_follow_tag (pub : LiteralTranscript.Public) (root : State)
    (T : Table Bytes State) (tr : List (Bytes × State))
    (own : BS Bytes State (List State)) (pend : List (Bytes × Option State))
    (g : List State → List State → RawLiteralDecoderDensity.LiteralOutput)
    (out : RawLiteralDecoderDensity.LiteralOutput)
    (hd : RecordedBinaryExperimentBin.dec (PublicInitFrame.frame pub.pubBytes root) T =
      some (own,pend,g))
    (hf : bfollow g tr own pend T = some out) : out.1.statement.tag = 2 := by
  let pub2 : LiteralTranscript.Public := ⟨pub.pubBytes, pub.initFits, 2⟩
  let a := PublicInitFrame.addr pub.pubBytes pub.initFits root
  have ha : CanonicalByteAddress.Canonical a := CanonicalByteAddress.canonical_ofBytes _ _
  let ac : AddrC SelectedTranscriptParams.L := ⟨a,ha⟩
  have hlen : pub2.pubBytes.length < 2^32 := by
    have h := pub.initFits
    change 75 + pub.pubBytes.length ≤ 131072 at h
    change pub.pubBytes.length < 2^32
    omega
  have hab : toBytes ac = PublicInitFrame.frame pub.pubBytes root := by
    change a.toBytes = _
    unfold a PublicInitFrame.addr
    rw [Addr.toBytes_ofBytes]
  have hselect : RawFullPublicSelection.select (PublicInitFrame.frame pub.pubBytes root) T = some pub2 := by
    unfold RawFullPublicSelection.select
    rw [← hab, RawPublicSelectionLift.of_canonical]
    exact FullPublicSelection.initial _ pub2 root hlen rfl _
  change RawAdaptiveLiteralDecoder.decode _ _ _ T = _ at hd
  rw [RawAdaptiveLiteralDecoder.decode_of_public _ _ _ _ _ hselect] at hd
  unfold RawLiteralDecoderDensity.decode at hd
  cases hr : RawUnifiedDecoder.decode SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub2
      (PublicInitFrame.frame pub.pubBytes root) T with
  | none => simp [hr] at hd
  | some result =>
    obtain ⟨s,ps,bg⟩ := result
    simp only [hr, Option.map_some] at hd
    cases hd
    obtain ⟨x,extra,he⟩ := follow_range _ _ _ _ _ _ hf
    rw [← he]
    change (bg x extra).1.statement.tag = 2
    have hp : PublicInitParse.parse pub2.pubBytes ac.val = some root :=
      PublicInitParse.parse_addr pub2.pubBytes hlen pub2.initFits root
    have hpoint := raw_pointwise pub2 ac T _ _ bg (by simpa only [hab] using hr) (by rw [hp]; rfl)
    rw [hpoint x extra]

#print axioms follow_range
#print axioms raw_pointwise
#print axioms initial_follow_tag
end AspisR1.RWireInitialTag
end
