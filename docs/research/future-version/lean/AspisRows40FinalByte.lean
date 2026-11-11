import FullPublicSelection
import RawLiteralDecoderDensity
import LiteralTableWordChoiceBin
import RawPublicSelectionLift
import AspisRows40Final

/-! Aspis one-transaction verifier: the byte-level decoder of rows 33 to 39,
the concrete `fin` of `Starts.decAspis`.

Copy of R1's byte chain for one component: R1's `RawUnifiedDecoder.atCanonical`
(canonical inputs only, own and pending addresses moved to bytes by
`RawBackgroundCompletion`, with the canonical-address lemma
`Final.component_good` in place of `UnifiedDecoderCanonical.decode_good`),
R1's `RawLiteralDecoderDensity.decode` (outputs restored with the word choice
`LiteralTableWordChoiceBin.choose`, as R1's `dec`), and R1's
`RawAdaptiveLiteralDecoder.decode` (the public statement selected from the
input and the table).

Public selection. R1's `FullPublicSelection.select` treats every frame whose
label row is at least 32 as a row-32 frame. For a frame of row n ≥ 33 this
selector walks back `n - 33` plain rows to row 32's absorb frame (as the
context parser does) and applies R1's selector there. -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.FinalByte
open FS FS2 FS2.Duplex R0C.V3
open AspisR1 AspisR1.TranscriptView
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CanonicalAddressEmbedding

abbrev p := SelectedTranscriptParams.params
abbrev L := SelectedTranscriptParams.L

theorem hD : 5 ≤ p.D := by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]

/-- The byte decoder type of R1's `RecordedBinaryExperimentBin.dec`. -/
abbrev BDec := Dec LiteralTranscript.Public LiteralTranscript.Message
  LiteralTranscript.Challenge Bytes State (List State)

/-- Public selection for a frame of row n ≥ 33. -/
def select (n : Nat) (a : Addr L) (T : Table (Addr L) State) : Option (UnifiedSampler.Public L) :=
  (parseAbsorb a).bind fun parsed =>
    (Context.back p T (n - 33) parsed.1).bind fun w => FullPublicSelection.select p w.1 T

/-- Copy of `RawUnifiedDecoder.atCanonical` for the final component. -/
def atCanonical (pub : UnifiedSampler.Public L) (n : Nat) (a : AddrC L) (T : Table Bytes State) :
    Option (RawUnifiedDecoder.Completion SelectedTranscriptParams.Message LiteralTranscript.E L) :=
  match hd : Final.component p pub n a.val (RawBoundedTrace.table L T) with
  | none => none
  | some (s, ps, g) =>
      let hg := Final.component_good p pub n a.val a.property (RawBoundedTrace.table L T) s ps g hd
      some (RawBackgroundCompletion.own s hg.1, RawBackgroundCompletion.pending ps hg.2, g)

/-- The concrete final-sumcheck byte decoder of rows 33 to 39. -/
def fin (n : Nat) : BDec := fun a T =>
  (RawPublicSelectionLift.select L (select n) a T).bind fun pub =>
    ((CanonicalRawTrace.decode L a).bind fun ac => atCanonical pub n ac T).map fun r =>
      (r.1, r.2.1, fun x as =>
        RawLiteralDecoderDensity.restore (LiteralTableWordChoiceBin.choose a T) (r.2.2 x as))

theorem atCanonical_of_component (pub : UnifiedSampler.Public L) (n : Nat) (a : AddrC L)
    (T : Table Bytes State)
    (s : BS (Addr L) State (List State)) (ps : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output SelectedTranscriptParams.Message
      LiteralTranscript.E L)
    (hd : Final.component p pub n a.val (RawBoundedTrace.table L T) = some (s, ps, g)) :
    let hg := Final.component_good p pub n a.val a.property (RawBoundedTrace.table L T) s ps g hd
    atCanonical pub n a T =
      some (RawBackgroundCompletion.own s hg.1, RawBackgroundCompletion.pending ps hg.2, g) := by
  dsimp only
  unfold atCanonical
  split
  · rename_i hn
    rw [hd] at hn
    cases hn
  · rename_i bs bp bg he
    have heq := Option.some.inj (he.symm.trans hd)
    cases heq
    rfl

/-- Byte-level bound, copy of `RawUnifiedDecoder.decoded_bound` composed with
`RawLiteralDecoderDensity`'s restore map: a fixed-prefix bound on row n's
sampler, for every selected statement, every canonical reading of the input
and every parsed context, bounds the background law of `fin n`'s output. -/
theorem fin_bound (n : Nat) (hlo : 33 ≤ n) (a : Bytes) (T : Table Bytes State)
    (own : BS Bytes State (List State)) (pend : List (Bytes × Option State))
    (g : List State → List State → RawLiteralDecoderDensity.LiteralOutput)
    (hd : fin n a T = some (own, pend, g))
    (obs : RawLiteralDecoderDensity.LiteralOutput → ℚ) (B : ℚ)
    (hfixed : ∀ (pub : UnifiedSampler.Public L) (c : Addr L), c.toBytes = a →
      ∀ ctx, Context.parse p pub.pubBytes pub.tag n c (RawBoundedTrace.table L T) = some ctx →
      ∀ as, as.length = (Final.missing p (RawBoundedTrace.table L T) ctx).length →
        independentMean
          (UnifiedSampler.samp p hD n (Final.prefixOf p pub (RawBoundedTrace.table L T) ctx as)
            (.payload ctx.message)).toProgram
          (fun w => obs (RawLiteralDecoderDensity.restore (LiteralTableWordChoiceBin.choose a T)
            (Final.prefixOf p pub (RawBoundedTrace.table L T) ctx as, .payload ctx.message, w.2)))
          ≤ B) :
    blaw g obs own pend ≤ B := by
  unfold fin at hd
  cases hs : RawPublicSelectionLift.select L (select n) a T with
  | none => simp [hs] at hd
  | some pub =>
      simp only [hs, Option.bind_some] at hd
      cases hc : CanonicalRawTrace.decode L a with
      | none => simp [hc] at hd
      | some ac =>
          simp only [hc, Option.bind_some] at hd
          have hb : ac.val.toBytes = a := (CanonicalRawTrace.decode_iff L a ac).1 hc
          cases hcomp : Final.component p pub n ac.val (RawBoundedTrace.table L T) with
          | none =>
              have : atCanonical pub n ac T = none := by
                unfold atCanonical
                split
                · rfl
                · rename_i bs bp bg he
                  rw [hcomp] at he
                  cases he
              rw [this] at hd
              cases hd
          | some result =>
              rcases result with ⟨s, ps, g0⟩
              rw [atCanonical_of_component pub n ac T s ps g0 hcomp] at hd
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨rfl, rfl, rfl⟩ := hd
              rw [BackgroundLawMap.blaw_map, RawBackgroundCompletion.blaw_eq]
              exact Final.component_bound p hD pub n hlo ac.val (RawBoundedTrace.table L T)
                s ps g0 hcomp _ B (fun ctx hp as has => hfixed pub ac.val hb ctx hp as has)

/-- `fin n` decodes when the statement is selected and the context parses. -/
theorem fin_isSome (n : Nat) (c : Addr L) (T : Table Bytes State) (pub : UnifiedSampler.Public L)
    (ctx : Context.Context SelectedTranscriptParams.Message L)
    (hc : CanonicalByteAddress.Canonical c)
    (hs : select n c (RawBoundedTrace.table L T) = some pub)
    (hp : Context.parse p pub.pubBytes pub.tag n c (RawBoundedTrace.table L T) = some ctx) :
    fin n c.toBytes T ≠ none := by
  have hdec : CanonicalRawTrace.decode L c.toBytes = some ⟨c, hc⟩ :=
    (CanonicalRawTrace.decode_iff L c.toBytes ⟨c, hc⟩).2 rfl
  have hsel : RawPublicSelectionLift.select L (select n) c.toBytes T = some pub := by
    simp only [RawPublicSelectionLift.select, hdec, Option.bind_some]
    exact hs
  have hcomp : Final.component p pub n c (RawBoundedTrace.table L T) ≠ none := by
    unfold Final.component DecoderStateList.lift
    rw [Final.decode_of_parse p pub n c _ ctx hp]
    simp
  cases hk : Final.component p pub n c (RawBoundedTrace.table L T) with
  | none => exact absurd hk hcomp
  | some result =>
      rcases result with ⟨s, ps, g0⟩
      have ha := atCanonical_of_component pub n ⟨c, hc⟩ T s ps g0 hk
      unfold fin
      rw [hsel, Option.bind_some, hdec, Option.bind_some, ha]
      simp

#print axioms hD
#print axioms atCanonical_of_component
#print axioms fin_bound
#print axioms fin_isSome

end AspisRows40.FinalByte
end
