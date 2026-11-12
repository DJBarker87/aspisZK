import AspisClassifier40
import AspisRowCharge
import AspisRows40FinalDensity
import AspisRows40FinalByte
import AspisRows40FinalStarts

/-! Plan item 9: piece (b) for the Aspis 40-row byte decoder
`AspisRows40.FinalStarts.decFinal = decAspis FinalByte.fin`.

Every decoded start of `decFinal` has classifier mass (Aspis classifier
`bad decodePair`) at most `charge40 a T`, a function of the address and the
pre-read table:

* frames R1's decoder decodes: R1's class cap (`AspisRowCharge.charge`),
  through a copy of `AspisRowCharge.literal_decoded_classifier_le_class` with
  the Aspis classifier (rows 0 to 31 R1's events, row 32 the residual pair,
  whose budget `capPair` is R1's row-32 budget);
* frames of rows 33 to 39 (`Starts.finalRow a = some n`): `capLambda` at 33,
  `capRound` at 34 to 39, through the rows agent's `FinalByte.fin_bound` and
  the row-densities agent's `Sampler.{combining,round}_unified_density`, with
  the bad sets `S33`, `SR n` read by `read33`, `readR` (AspisClassifier40)
  from the restored prefix and message.

Kind of result: probability bound about the decoder and classifier (the level
of R1's `adaptive_decoded_classifier_le`). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AspisCharge40
open scoped BigOperators
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1 AspisR1.TranscriptView
open AspisAcceptance AspisClassifier40 AspisPerStep.RowCharge
open AspisRowDensity.QM31 AspisRowDensity.Sampler
open CanonicalAddressEmbedding

/-- The Aspis classifier in the decoder's shape (the table is not read). -/
def classifier40 (decodePair : Codec) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (_T : Table Bytes State) (c : LiteralTranscript.Challenge) :
    Prop :=
  bad decodePair P m c

theorem budget40_le_classCap (i n : Nat) (hi : i < 33) (h : cls i = cls n) :
    budget40 i ≤ classCap n := by
  by_cases h32 : i < 32
  · rw [budget40_lt32 i h32]
    exact budget_le_classCap i n hi h
  · obtain rfl : i = 32 := by omega
    rw [budget40_32]
    exact budget_le_classCap 32 n hi h

open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript RawLiteralDecoderDensity in
/-- R1 frames: copy of `AspisRowCharge.literal_decoded_classifier_le_class`
for the Aspis classifier. -/
theorem literal_le_class (decodePair : Codec) (choose : WordChoice) (pub : LiteralTranscript.Public)
    (a : Bytes) (T : Table Bytes State) own pend g
    (hd : RawLiteralDecoderDensity.decode choose pub a T = some (own, pend, g)) :
    blaw g (fun out => indicator (classifier40 decodePair out.1 out.2.1 T out.2.2))
      own pend ≤ classCap (rawRow pub a) := by
  unfold RawLiteralDecoderDensity.decode at hd
  cases hc : RawUnifiedDecoder.decode SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a T with
  | none => simp [hc] at hd
  | some result =>
    rcases result with ⟨bs, bp, bg⟩
    simp only [hc, Option.map_some] at hd
    have hbound : blaw bg (fun out => indicator
        (classifier40 decodePair (restore (choose a T) out).1
          (restore (choose a T) out).2.1 T (restore (choose a T) out).2.2)) bs bp ≤
        classCap (rawRow pub a) := by
      refine raw_decoded_bound_class SelectedTranscriptParams.params
        (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        pub a T bs bp bg hc _ (classCap (rawRow pub a)) ?_
      intro i P m hi hround hcls
      subst i
      exact (erased_density decodePair (choose a T P m) P m hi).trans
        (budget40_le_classCap P.round (rawRow pub a) hi hcls)
    cases hd
    rw [BackgroundLawMap.blaw_map]
    exact hbound

/-- R1 frames through R1's adaptive decoder. -/
theorem adaptive_le_charge (decodePair : Codec)
    (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice) (words : RawLiteralDecoderDensity.WordChoice)
    (a : Bytes) (T : Table Bytes State) own pend g
    (hd : RawAdaptiveLiteralDecoder.decode pubChoice words a T = some (own, pend, g)) :
    blaw g (fun out => indicator (classifier40 decodePair out.1 out.2.1 T out.2.2))
      own pend ≤ charge pubChoice a T := by
  unfold RawAdaptiveLiteralDecoder.decode at hd
  cases hp : pubChoice a T with
  | none => simp [hp] at hd
  | some pub =>
    simp only [hp, Option.bind_some] at hd
    simp only [charge, hp]
    exact literal_le_class decodePair words pub a T own pend g hd

/-- The cap of a frame of row `n` (33 to 39). -/
def finalCap (n : Nat) : ℚ := if n = 33 then capLambda else capRound

open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript in
/-- Row 33's read through the restore map of the start `(a, T)`. -/
def read33' (decodePair : Codec) (a : Bytes) (T : Table Bytes State)
    (Pm : ErasedPrefix × ErasedMessage) : Option X33 :=
  read33 decodePair (restorePrefix (LiteralTableWordChoiceBin.choose a T Pm.1 Pm.2) Pm.1)
    (message (LiteralTableWordChoiceBin.choose a T Pm.1 Pm.2) Pm.1.round Pm.2)

open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript in
/-- Rows 34 to 39's read through the restore map of the start `(a, T)`. -/
def readR' (decodePair : Codec) (a : Bytes) (T : Table Bytes State)
    (Pm : ErasedPrefix × ErasedMessage) : Option XR :=
  readR decodePair (restorePrefix (LiteralTableWordChoiceBin.choose a T Pm.1 Pm.2) Pm.1)
    (message (LiteralTableWordChoiceBin.choose a T Pm.1 Pm.2) Pm.1.round Pm.2)

open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript RawLiteralDecoderDensity in
/-- Frames of rows 33 to 39: the decoded start of `FinalByte.fin n` has
classifier mass at most `finalCap n`. -/
theorem fin_le (decodePair : Codec) (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40)
    (a : Bytes) (T : Table Bytes State)
    (own : BS Bytes State (List State)) (pend : List (Bytes × Option State))
    (g : List State → List State → RawLiteralDecoderDensity.LiteralOutput)
    (hd : AspisRows40.FinalByte.fin n a T = some (own, pend, g)) :
    blaw g (fun out => indicator (classifier40 decodePair out.1 out.2.1 T out.2.2))
      own pend ≤ finalCap n := by
  apply AspisRows40.FinalByte.fin_bound n hlo a T own pend g hd
  intro pub c _ ctx hp ans _
  -- the prefix and message of row n
  have hlen := AspisRows40.Final.prefixOf_length AspisRows40.FinalByte.p pub
    (RawBoundedTrace.table AspisRows40.FinalByte.L T) n hlo c ctx hp ans
  set P := AspisRows40.Final.prefixOf AspisRows40.FinalByte.p pub
    (RawBoundedTrace.table AspisRows40.FinalByte.L T) ctx ans with hP
  set m : TranscriptView.Message SelectedTranscriptParams.Message := .payload ctx.message with hm
  have hround : P.round = n := hlen
  have hround' : (restorePrefix (LiteralTableWordChoiceBin.choose a T P m) P).round = n := by
    rw [prefix_round]; exact hround
  by_cases h33 : n = 33
  · subst h33
    have hread : ∀ Pm, read33' decodePair a T Pm = read33 decodePair
        (restorePrefix (LiteralTableWordChoiceBin.choose a T Pm.1 Pm.2) Pm.1)
        (message (LiteralTableWordChoiceBin.choose a T Pm.1 Pm.2) Pm.1.round Pm.2) := fun _ => rfl
    have hpt : ∀ ch : LiteralTranscript.Challenge,
        indicator (classifier40 decodePair
          (restore (LiteralTableWordChoiceBin.choose a T) (P, m, ch)).1
          (restore (LiteralTableWordChoiceBin.choose a T) (P, m, ch)).2.1 T
          (restore (LiteralTableWordChoiceBin.choose a T) (P, m, ch)).2.2) =
        indicator (ordEvent (setBad (read33' decodePair a T) S33 (P, m)) ch) := by
      intro ch
      apply indicator_iff
      simp only [restore, classifier40]
      rw [bad_ge33 _ _ _ (by rw [hround'])]
      unfold finalBad ordEvent setBad
      rcases ch with ⟨v, s⟩
      cases v with
      | ordinary x =>
        dsimp only
        rw [finalEvent_iff33 decodePair _ _ _ hround', hread]
        dsimp only
        generalize read33 decodePair (restorePrefix (LiteralTableWordChoiceBin.choose a T P m) P)
          (message (LiteralTableWordChoiceBin.choose a T P m) P.round m) = r
        cases r <;> exact Iff.rfl
      | queries _ => exact Iff.rfl
    simp only [hpt]
    have h := combining_unified_density (read33' decodePair a T) S33 S33_card AspisRows40.FinalByte.p
      AspisRows40.FinalByte.hD 33 P m (by omega)
      (AspisRows40.Final.messageValid_final 33 le_rfl _)
      (AspisRows40.Protocol.final_sigma_rho 33 (by omega))
    simpa [finalCap] using h
  · have h34 : 34 ≤ n := by omega
    have hread : ∀ Pm, readR' decodePair a T Pm = readR decodePair
        (restorePrefix (LiteralTableWordChoiceBin.choose a T Pm.1 Pm.2) Pm.1)
        (message (LiteralTableWordChoiceBin.choose a T Pm.1 Pm.2) Pm.1.round Pm.2) := fun _ => rfl
    have hpt : ∀ ch : LiteralTranscript.Challenge,
        indicator (classifier40 decodePair
          (restore (LiteralTableWordChoiceBin.choose a T) (P, m, ch)).1
          (restore (LiteralTableWordChoiceBin.choose a T) (P, m, ch)).2.1 T
          (restore (LiteralTableWordChoiceBin.choose a T) (P, m, ch)).2.2) =
        indicator (ordEvent (setBad (readR' decodePair a T) (SR n) (P, m)) ch) := by
      intro ch
      apply indicator_iff
      simp only [restore, classifier40]
      rw [bad_ge33 _ _ _ (by rw [hround']; omega)]
      unfold finalBad ordEvent setBad
      rcases ch with ⟨v, s⟩
      cases v with
      | ordinary x =>
        dsimp only
        rw [finalEvent_iffR decodePair _ _ _ n hround' h34 hhi, hread]
        dsimp only
        generalize readR decodePair (restorePrefix (LiteralTableWordChoiceBin.choose a T P m) P)
          (message (LiteralTableWordChoiceBin.choose a T P m) P.round m) = r
        cases r <;> exact Iff.rfl
      | queries _ => exact Iff.rfl
    simp only [hpt]
    have h := round_unified_density (readR' decodePair a T) (SR n) (SR_card n) AspisRows40.FinalByte.p
      AspisRows40.FinalByte.hD n P m (by omega)
      (AspisRows40.Final.messageValid_final n hlo _)
      (AspisRows40.Protocol.final_sigma_rho n (by omega))
    simpa [finalCap, h33] using h

/-- Piece (b) for the 40-row decoder: the charge of a decoded start. -/
def charge40 (a : Bytes) (T : Table Bytes State) : ℚ :=
  match AspisRows40.Starts.finalRow a with
  | some n => finalCap n
  | none => charge RawFullPublicSelection.select a T

/-- Piece (b) for `decFinal`. -/
theorem decFinal_le_charge40 (decodePair : Codec) (a : Bytes) (T : Table Bytes State) own pend g
    (hd : AspisRows40.FinalStarts.decFinal a T = some (own, pend, g)) :
    blaw g (fun out => indicator (classifier40 decodePair out.1 out.2.1 T out.2.2))
      own pend ≤ charge40 a T := by
  unfold charge40
  cases hf : AspisRows40.Starts.finalRow a with
  | some n =>
    obtain ⟨_, _, _, _, _, hlo, hhi⟩ := AspisRows40.Starts.finalRow_sound a n hf
    have he := AspisRows40.Starts.decAspis_final AspisRows40.FinalByte.fin a T n hf
    unfold AspisRows40.FinalStarts.decFinal at hd
    rw [he] at hd
    exact fin_le decodePair n hlo hhi a T own pend g hd
  | none =>
    unfold AspisRows40.FinalStarts.decFinal AspisRows40.Starts.decAspis at hd
    cases hdec : AspisR1.AspisLib.RecordedBinaryExperimentBin.dec a T with
    | none => simp [hdec, hf] at hd
    | some r =>
      rw [hdec] at hd
      simp only at hd
      rw [hd] at hdec
      exact adaptive_le_charge decodePair RawFullPublicSelection.select
        LiteralTableWordChoiceBin.choose a T own pend g hdec

#print axioms literal_le_class
#print axioms adaptive_le_charge
#print axioms fin_le
#print axioms decFinal_le_charge40
end AspisCharge40
end
