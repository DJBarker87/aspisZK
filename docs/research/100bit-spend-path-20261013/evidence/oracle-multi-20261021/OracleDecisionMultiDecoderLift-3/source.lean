import BinHonestStartFrames

/-! A symbolic decoder lift. Keeping the canonical address and current table
abstract avoids normalizing a concrete 131072-cell padded address. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiDecoderLift
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open CanonicalAddressEmbedding
abbrev p := SelectedTranscriptParams.params
abbrev L := SelectedTranscriptParams.L

theorem recognizes (pub : LiteralTranscript.Public) (a : AddrC L) (T : Table Bytes State)
    (hp : RawFullPublicSelection.select (toBytes a) T = some pub)
    (hu : UnifiedDecoder.decode p (by norm_num [p, SelectedTranscriptParams.params,
      SelectedTranscriptParams.D]) pub a.val (RawBoundedTrace.table L T) ≠ none) :
    RecordedBinaryExperimentBin.dec (toBytes a) T ≠ none := by
  unfold RecordedBinaryExperimentBin.dec
  rw [RawAdaptiveLiteralDecoder.decode_of_public _ _ _ _ _ hp]
  unfold RawLiteralDecoderDensity.decode
  rw [RawUnifiedDecoder.decode_of_canonical p _ pub a T]
  cases he : UnifiedDecoder.decode p _ pub a.val (RawBoundedTrace.table L T) with
  | none => exact False.elim (hu he)
  | some result =>
      rcases result with ⟨s, ps, g⟩
      rw [RawUnifiedDecoder.atCanonical_of_decode p
        (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a T s ps g he]
      simp only [Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]

theorem public_walk_one {M Cv : Type} {N : Nat} (q : Params M Cv N)
    (T : Table (Addr N) State) (fuel : Nat) (prev absorbed endpoint : State)
    (label : AspisV8R19.DuplexFrames.Byte) (data : Bytes) (a : Addr N) (pub : UnifiedSampler.Public N) (c1 : State)
    (had : theUnique (advPre q T endpoint) = some absorbed)
    (hac : ReseedBoundary.findCell T absorbed = some a)
    (hap : parseAbsorb a = some (prev,label,data))
    (hr : InitialPublicWalk.rootAt T prev = some (pub,c1)) :
    InitialPublicWalk.walk q T (fuel+1) endpoint =
      some ((pub,c1), [⟨prev,absorbed,label,data,endpoint⟩]) := by
  rw [InitialPublicWalk.walk, had]
  dsimp only
  rw [hac]
  dsimp only
  rw [hap]
  dsimp only
  rw [hr]

theorem fixed_walk_one {M Cv : Type} {N : Nat} (q : Params M Cv N)
    (T : Table (Addr N) State) (fuel : Nat) (prev absorbed endpoint : State)
    (label : AspisV8R19.DuplexFrames.Byte) (data pubBytes : Bytes) (a : Addr N) (c1 : State)
    (had : theUnique (advPre q T endpoint) = some absorbed)
    (hac : ReseedBoundary.findCell T absorbed = some a)
    (hap : parseAbsorb a = some (prev,label,data))
    (hr : InitialWalk.rootAt pubBytes T prev = some c1) :
    InitialWalk.walk q pubBytes T (fuel+1) endpoint =
      some (c1, [⟨prev,absorbed,label,data,endpoint⟩]) := by
  rw [InitialWalk.walk, had]
  dsimp only
  rw [hac]
  dsimp only
  rw [hap]
  dsimp only
  rw [hr]

/-- Abstract semantic recognition; never normalize a concrete decoder output. -/
theorem semantic_recognizes (pub : LiteralTranscript.Public) (a : AddrC L)
    (T : Table Bytes State) (endpoint : State) (label : AspisV8R19.DuplexFrames.Byte) (data : Bytes)
    (ctx : UnifiedSemanticContext.Context SelectedTranscriptParams.Message)
    (hp : RawFullPublicSelection.select (toBytes a) T = some pub)
    (hi : PublicInitParse.parse pub.pubBytes a.val = none)
    (ha : parseAbsorb a.val = some (endpoint,label,data))
    (hl : UnifiedLabels.row label = 1)
    (hc : UnifiedSemanticContext.parse p pub.pubBytes a.val (RawBoundedTrace.table L T) = some ctx)
    (hlo : 0 < ctx.records.length) (hhi : ctx.records.length < 26) :
    RecordedBinaryExperimentBin.dec (toBytes a) T ≠ none := by
  apply recognizes pub a T hp
  have hd := UnifiedSemanticDecoder.decode_of_parse p pub a.val (RawBoundedTrace.table L T)
    ctx hc hlo hhi
  simp only [UnifiedDecoder.decode, hi, Option.isSome_none, Bool.false_eq_true, if_false,
    ha, Option.bind_some, hl]
  rw [UnifiedDecoder.component_semantic p _ pub 1 (by decide) (by decide)]
  simp only [DecoderStateList.lift, hd, Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]

#print axioms public_walk_one
#print axioms fixed_walk_one
#print axioms semantic_recognizes
#print axioms recognizes
end AspisR1.OracleDecisionMultiDecoderLift
end
