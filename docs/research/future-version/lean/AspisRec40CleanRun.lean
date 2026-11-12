import Frozen2StartChargeCompletion
import TraceAppend
import R1FollowAppend
import StartChargeHit
import AspisRec40Frames
import AspisRec40CleanStatement

/-! Aspis 40-row clean event, run-structure part: the charged run against
R1's charged run, decoding of rows 0 to 32 transported from R1's
`Frozen2StartChargeCompletion.decodes`, all-40-row decoding given the rows
33-to-39 part (`FinalDecodes`), and the hit-in-prefix lemma.

`base_split`: the Aspis base run is R1's base run followed by the chains of
rows 33 to 39, with the same output. R1's `decodes` is applied to R1's base
run (its premises follow from the Aspis ones on the longer trace) and its
conclusion is carried to the longer trace (`TraceAppend`,
`FollowAppend.bfollow_append_of_some`) and to the Aspis decoder
(`Starts.decAspis_of_r1`). No R1 constant from a two-transaction module is
used (R1's `prefix_chain_read`, which goes through `same_transcript`, is not
used; the read is proved from `RawCutWordsFromView.frame_read`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CleanRun
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1
open RawCutWordsFromView (frame frameFromView)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D
abbrev r1base (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) := eval H (Frozen2StartChargePrefix.base D P)
abbrev base (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) := eval H (AspisRec40.ChargePrefix.base D P)

theorem chains_eq (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) :
    (fun j => (eval H ((pr D).chain H pub pf j).toProgram).1) =
      (fun j => (eval H ((LiteralByteProtocol.protocol D).chain H pub pf j).toProgram).1) := by
  funext j
  rw [AspisRows40.Protocol.chain_eq]

/-- The Aspis base run is R1's base run followed by the chains of rows 33 to 39. -/
theorem base_split (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) :
    (∃ tail, (base D P H).1 = (r1base D P H).1 ++ tail) ∧ (base D P H).2.1 = (r1base D P H).2.1 := by
  unfold base r1base AspisRec40.ChargePrefix.base Frozen2StartChargePrefix.base
  rw [RawCutProverCompiler.experiment_eval, RawCutProverCompiler.experiment_eval,
    AspisRows40.Starts.verifier, RawCutProverCompiler.verifier, FS2.verifier_eval, FS2.verifier_eval]
  refine ⟨?_, rfl⟩
  dsimp only
  rw [show (AspisRows40.Protocol.protocol D).r = 33 + 7 from rfl, List.range_add,
    List.map_append, List.flatten_append, chains_eq]
  exact ⟨_, by rw [List.append_assoc]; rfl⟩

theorem frame_read_r1 (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) (n : Nat) (hn : n < 33) :
    Read (r1base D P H).1 (frame D H (r1base D P H).2.1.1 (r1base D P H).2.1.2 n) :=
  RawCutWordsFromView.frame_read D (fun _ _ => true) (Frozen2StartChargePrefix.prover P) H n hn

theorem words_base_eq (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) :
    BinCompiledRunWordStability.wordsFromRun D (base D P H) =
      BinCompiledRunWordStability.wordsFromRun D (r1base D P H) := by
  obtain ⟨⟨tail, ht⟩, hs⟩ := base_split D P H
  have hf (n : Nat) (hn : n < 33) :
      frameFromView D (base D P H) n = frameFromView D (r1base D P H) n := by
    have a : frameFromView D (base D P H) n =
        frame D H (base D P H).2.1.1 (base D P H).2.1.2 n := by
      change frameFromView D (AspisRec40.Decision.base D (AspisRec40.ChargePrefix.prover P) H) n = _
      rw [AspisRec40.Frames.base_lift]
      exact AspisRec40.Frames.frameFromView_eq D _ _ H n (by omega)
    have b : frameFromView D (r1base D P H) n =
        frame D H (r1base D P H).2.1.1 (r1base D P H).2.1.2 n :=
      RawCutWordsFromView.frameFromView_eq D (fun _ _ => true) (Frozen2StartChargePrefix.prover P) H n (by omega)
    rw [a, b, hs]
  have hc (n : Nat) (hn : n < 33) :
      BinRawByteCutRecovery.cut (base D P H).1 (frameFromView D (r1base D P H) n) =
        BinRawByteCutRecovery.cut (r1base D P H).1 (frameFromView D (r1base D P H) n) := by
    rw [ht]
    apply OracleProgramRecording.cut_append_of_read
    rw [RawCutWordsFromView.frameFromView_eq D (fun _ _ => true) (Frozen2StartChargePrefix.prover P) H n (by omega)]
    exact frame_read_r1 D P H n hn
  unfold BinCompiledRunWordStability.wordsFromRun
  rw [hf 0 (by decide), hf 2 (by decide), hf 30 (by decide)]
  unfold BinCanonicalCutWords.wordsFromRawCuts BinCanonicalCutWords.rawC1Map
    BinCanonicalCutWords.rawC2Map BinCanonicalCutWords.rawFoldedMap
  dsimp only
  rw [hc 0 (by decide), hc 2 (by decide), hc 30 (by decide)]

/-- The Aspis charged run is R1's charged run followed by rows 33 to 39, same output. -/
theorem charged_split (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) :
    (∃ tail, (eval H (AspisRec40.ChargePrefix.charged D P)).1 =
      (eval H (Frozen2StartChargePrefix.charged D P)).1 ++ tail) ∧
    (eval H (AspisRec40.ChargePrefix.charged D P)).2.1 =
      (eval H (Frozen2StartChargePrefix.charged D P)).2.1 := by
  obtain ⟨⟨tail, ht⟩, hs⟩ := base_split D P H
  rw [AspisRec40.ChargePrefix.charged_eval, Frozen2StartChargePrefix.charged_eval]
  refine ⟨⟨tail, ht⟩, ?_⟩
  change ((base D P H).2.1.1, RawCutTranscriptRun.proof
      (BinCompiledRunWordStability.wordsFromRun D (base D P H)) (base D P H).2.1.2) =
    ((r1base D P H).2.1.1, RawCutTranscriptRun.proof
      (BinCompiledRunWordStability.wordsFromRun D (r1base D P H)) (r1base D P H).2.1.2)
  rw [words_base_eq, hs]

theorem chal_eq (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (n : Nat) :
    (pr D).chal H pub pf n = (LiteralByteProtocol.protocol D).chal H pub pf n := by
  unfold FS2.Protocol.chal
  rw [AspisRows40.Protocol.chain_eq]

/-- R1's decoding of rows 0 to 32 (`Frozen2StartChargeCompletion.decodes`),
carried to the Aspis charged run and decoder. Premises: R1's, on the Aspis base run. -/
theorem decodes_r1rows (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) (Q : Nat)
    (hQ : firstReads emptyTable (base D P H).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (base D P H).1)
    (format : RWireCheckedFormat.Format (base D P H).2.1.2)
    (tag : (base D P H).2.1.1.tag = 2)
    (n : Nat) (a : Bytes) (hn : n < 33)
    (hfirst : firstCell ((pr D).chain H (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.1
      (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.2 n) = some a) :
    let v := eval H (AspisRec40.ChargePrefix.charged D P)
    ∃ own pend g, AspisRows40.FinalStarts.decFinal a (tableBefore emptyTable v.1 a) =
        some (own,pend,g) ∧
      bfollow g (traceFrom v.1 a) own pend (tableBefore emptyTable v.1 a) =
        some ((pr D).transcript H v.2.1.1 v.2.1.2 n, (pr D).msg v.2.1.2 n,
          (pr D).chal H v.2.1.1 v.2.1.2 n) := by
  intro v
  obtain ⟨⟨tail, ht⟩, hs⟩ := base_split D P H
  obtain ⟨⟨ctail, hct⟩, hcs⟩ := charged_split D P H
  have hQR : firstReads emptyTable (r1base D P H).1 ≤ Q :=
    (TraceAppend.firstReads_le_append emptyTable _ tail).trans (by rw [← ht]; exact hQ)
  have houtR : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (r1base D P H).1 := by
    intro h
    apply hout
    rw [ht]
    exact TraceAppend.hitsBad_of_prefix _ _ _ _ h
  have formatR : RWireCheckedFormat.Format (r1base D P H).2.1.2 := by rw [← hs]; exact format
  have tagR : (r1base D P H).2.1.1.tag = 2 := by rw [← hs]; exact tag
  have hd := Frozen2StartChargeCompletion.decodes D P H Q hQR houtR formatR tagR
  have hfirst' : firstCell ((LiteralByteProtocol.protocol D).chain H
      (eval H (Frozen2StartChargePrefix.charged D P)).2.1.1
      (eval H (Frozen2StartChargePrefix.charged D P)).2.1.2 n) = some a := by
    rw [← hcs, ← AspisRows40.Protocol.chain_eq]
    exact hfirst
  obtain ⟨own,pend,g,hdec,hfol⟩ := hd n a hn hfirst'
  have hread : a ∈ (eval H (Frozen2StartChargePrefix.charged D P)).1.map Prod.fst := by
    have hf2 := hfirst'
    rw [Frozen2StartChargePrefix.charged_eval] at hf2 ⊢
    dsimp only at hf2 ⊢
    rw [RawCutTranscriptRun.chain_eq] at hf2
    have he : frame D H (r1base D P H).2.1.1 (r1base D P H).2.1.2 n = a := by
      unfold frame
      rw [hf2]
      rfl
    rw [← he]
    exact frame_read_r1 D P H n hn
  have hT : tableBefore emptyTable v.1 a =
      tableBefore emptyTable (eval H (Frozen2StartChargePrefix.charged D P)).1 a := by
    change tableBefore emptyTable (eval H (AspisRec40.ChargePrefix.charged D P)).1 a = _
    rw [hct]
    exact TraceAppend.tableBefore_append _ _ _ _ hread
  have hTr : traceFrom v.1 a =
      traceFrom (eval H (Frozen2StartChargePrefix.charged D P)).1 a ++ ctail := by
    change traceFrom (eval H (AspisRec40.ChargePrefix.charged D P)).1 a = _
    rw [hct]
    exact TraceAppend.traceFrom_append _ _ _ hread
  refine ⟨own, pend, g, ?_, ?_⟩
  · rw [hT]
    unfold AspisRows40.FinalStarts.decFinal
    rw [AspisRows40.Starts.decAspis_of_r1 _ _ _
      (by rw [show AspisR1.AspisLib.RecordedBinaryExperimentBin.dec _ _ = _ from hdec]; simp)]
    exact hdec
  · rw [hT, hTr]
    have hfa := FollowAppend.bfollow_append_of_some g _ ctail own pend _ _ hfol
    rw [hfa]
    change some ((LiteralByteProtocol.protocol D).transcript H
        (eval H (Frozen2StartChargePrefix.charged D P)).2.1.1
        (eval H (Frozen2StartChargePrefix.charged D P)).2.1.2 n,
      (LiteralByteProtocol.protocol D).msg (eval H (Frozen2StartChargePrefix.charged D P)).2.1.2 n,
      (LiteralByteProtocol.protocol D).chal H (eval H (Frozen2StartChargePrefix.charged D P)).2.1.1
        (eval H (Frozen2StartChargePrefix.charged D P)).2.1.2 n) = _
    rw [← hcs, chal_eq, ← AspisRows40.Protocol.transcript_eq]
    rfl

/-- Decoding of all 40 rows of the charged run. -/
def Decodes40 (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (v : RawCutProverCompiler.RunView) : Prop :=
  ∀ n a, n < 40 → firstCell ((pr D).chain H v.2.1.1 v.2.1.2 n) = some a →
    ∃ own pend g, AspisRows40.FinalStarts.decFinal a (tableBefore emptyTable v.1 a) =
      some (own,pend,g) ∧
      bfollow g (traceFrom v.1 a) own pend (tableBefore emptyTable v.1 a) =
        some ((pr D).transcript H v.2.1.1 v.2.1.2 n, (pr D).msg v.2.1.2 n,
          (pr D).chal H v.2.1.1 v.2.1.2 n)

theorem decodes40 (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) (Q : Nat)
    (hQ : firstReads emptyTable (base D P H).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (base D P H).1)
    (format : RWireCheckedFormat.Format (base D P H).2.1.2)
    (tag : (base D P H).2.1.1.tag = 2)
    (hfinal : AspisRec40.CleanStatement.FinalDecodes D H (eval H (AspisRec40.ChargePrefix.charged D P))) :
    Decodes40 D H (eval H (AspisRec40.ChargePrefix.charged D P)) := by
  intro n a hn hf
  by_cases h33 : n < 33
  · exact decodes_r1rows D P H Q hQ hout format tag n a h33 hf
  · exact hfinal n a (by omega) hn hf

/-- Every chain of the 40-row protocol has a first cell (`ChainsRead`). -/
theorem chains_read (D : LiteralByteProtocol.Decoder) : ChainsRead (pr D) := by
  intro i p m _
  have hmap {I J A C : Type} [DecidableEq I] [Inhabited A]
      (label : I → J) (s : Sampler I A C) :
      firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
    cases s <;> rfl
  change firstCell (ProgramSamplerMap.map Addr.toBytes (LiteralTranscript.samp i p m)) ≠ none
  rw [hmap]
  have hn : firstCell (LiteralTranscript.samp i p m) ≠ none :=
    UnifiedSampler.firstCell_some _ _ _ _ _
  cases h : firstCell (LiteralTranscript.samp i p m) with
  | none => exact absurd h hn
  | some a => simp

/-- Every chain start of the charged run is read in it. -/
theorem charged_reads (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) (n : Nat) (a : Bytes) (hn : n < 40)
    (hf : firstCell ((pr D).chain H (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.1
      (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.2 n) = some a) :
    a ∈ (eval H (AspisRec40.ChargePrefix.charged D P)).1.map Prod.fst := by
  rw [AspisRec40.ChargePrefix.charged_eval] at hf ⊢
  dsimp only at hf ⊢
  rw [AspisRows40.Protocol.chain_eq, RawCutTranscriptRun.chain_eq] at hf
  have he : frame D H (base D P H).2.1.1 (base D P H).2.1.2 n = a := by
    unfold frame
    rw [hf]
    rfl
  rw [← he]
  change Read (AspisRec40.Decision.base D (AspisRec40.ChargePrefix.prover P) H).1 _
  rw [AspisRec40.Frames.base_lift]
  exact AspisRec40.Frames.frame_read D _ _ H n hn

theorem classifier40_eq :
    AspisCharge40.classifier40 AspisOneTx.decodePairS =
      fun p m (_t : Table Bytes State) c => AspisAcceptance.bad AspisOneTx.decodePairS p m c := by
  funext p m t c
  rfl

attribute [local irreducible] AspisAcceptance.bad AspisRows40.Protocol.protocol
  R0C.V3.hitsChain3 GenericNoHit.hitFrom

/-- Copy of `Frozen2StartChargeCompletion.hit_in_prefix`, 33 → 40. -/
theorem hit_in_prefix (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State)
    (hdec : Decodes40 D H (eval H (AspisRec40.ChargePrefix.charged D P)))
    (hhit : GenericNoHit.hitFrom (AspisAcceptance.bad AspisOneTx.decodePairS)
      (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.1 []
      ((pr D).transcript H (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.1
        (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.2 (pr D).r).rounds) :
    hitsChain3 AspisRows40.FinalStarts.decFinal (AspisCharge40.classifier40 AspisOneTx.decodePairS)
      emptyTable (eval H (AspisRec40.ChargePrefix.charged D P)).1 := by
  rw [classifier40_eq]
  exact StartChargeHit.hit_implies_chain (pr D) (AspisAcceptance.bad AspisOneTx.decodePairS)
    AspisRows40.FinalStarts.decFinal H (eval H (AspisRec40.ChargePrefix.charged D P))
    (fun n a hn hf => charged_reads D P H n a (by simpa only [AspisRows40.Protocol.protocol_r] using hn) hf) (chains_read D)
    (fun n a hn hf => hdec n a (by simpa only [AspisRows40.Protocol.protocol_r] using hn) hf) hhit

#print axioms base_split
#print axioms words_base_eq
#print axioms charged_split
#print axioms decodes_r1rows
#print axioms decodes40
#print axioms chains_read
#print axioms charged_reads
#print axioms hit_in_prefix

end AspisRec40.CleanRun
end
