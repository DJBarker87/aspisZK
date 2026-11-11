import AspisRec40FinalBridge
import AspisRec40FinalWords
import AspisRec40CleanStatement
import AspisRows40FinalStarts

/-! The body of `AspisFailureBound.Joined.FinalDecoding40`, proved for every
decoder, prover and budget, with no further premise.

Copy of R1's `Frozen2StartChargeCompletion.decodes` (through
`RWireRawFullPublicRun.adaptive_run_decodes_and_follows` and
`RWireRawLiteralRecordedDecoder.actual_run_decodes_and_follows`) for rows 33 to
39. On the charged run's base run, under R1's four premises and `LatePayload`:
* the literal late-row form is `FinalLiteral.base_literal` (the base proof is
  R16-canonical);
* the words chosen from the table at row n's frame are the run's words (W3,
  `FinalWords.constructed_components40`);
* W4 (`FinalBridge.decodes_and_follows40`) gives `fin n`'s decoding and follow
  to the enriched prefix, message and challenge of the base proof, which are
  the charged run's (`RawCutTranscriptRun.transcript_eq`, `chain_eq`);
* `decFinal` dispatches row n's frame to `fin n` (`Starts.decAspis_final`,
  `finalRow_absorb`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalDecoding
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 LiteralLegacyRun
open CanonicalCutEnrichedTranscript

abbrev p := SelectedTranscriptParams.params

theorem final_decodes (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (H : Bytes → State)
    (hQ : firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred Q) emptyTable
        (eval H (AspisRec40.ChargePrefix.base D P)).1)
    (format : RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2)
    (tag : (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1.tag = 2)
    (hlate : AspisRec40.FinalShape.LatePayload (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2) :
    AspisRec40.CleanStatement.FinalDecodes D H (eval H (AspisRec40.ChargePrefix.charged D P)) := by
  obtain ⟨hv, r1, w1, b2, w2, r2, b30, w30, v30, h0, h2, h30, hp2, hp30⟩ := format
  have hlit := AspisRec40.FinalLiteral.base_literal D P H hlate
  have hv40 : AspisRec40.FinalLegacy.Valid40 (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 :=
    ⟨hv, hlit⟩
  intro n a hlo hhi hfirst
  rw [AspisRec40.ChargePrefix.charged_eval] at hfirst ⊢
  dsimp only at hfirst ⊢
  let Wd := BinCompiledRunWordStability.wordsFromRun D (eval H (AspisRec40.ChargePrefix.base D P))
  let draw := RawCutTranscriptRun.decisionOnBytes (fun _ _ => true)
  -- the base run's chain
  rw [AspisRows40.Protocol.chain_eq, RawCutTranscriptRun.chain_eq,
    ← AspisRows40.Protocol.chain_eq] at hfirst
  have htr : AspisRec40.FinalBridgeStatement.rawTrace40 D draw H
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2
      (eval H (AspisRec40.ChargePrefix.prover P)).1 =
      (eval H (AspisRec40.ChargePrefix.base D P)).1 := by
    unfold AspisRec40.FinalBridgeStatement.rawTrace40 AspisRec40.ChargePrefix.base
    rw [RawCutProverCompiler.experiment_eval]
    rfl
  -- W3: the table's word choice at row n's frame is the run's words
  have hw := AspisRec40.FinalWords.constructed_components40 D (fun _ _ => true)
    (AspisRec40.ChargePrefix.prover P) H (eval H (AspisRec40.ChargePrefix.base D P)) rfl
    SelectedTranscriptParams.params.iv Q hQ hout hv hlate n hlo hhi
    r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30
  dsimp only at hw
  have hframe := AspisRec40.Frames.frame_firstCell D H (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1
    (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 n
  rw [hfirst] at hframe
  have ha := (Option.some.inj hframe).symm
  rw [ha] at hw
  -- W4
  have hb := AspisRec40.FinalBridge.decodes_and_follows40 D draw H
    (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1
    (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 hv hlit tag
    (eval H (AspisRec40.ChargePrefix.prover P)).1
    (FS.eval_consistent H (AspisRec40.ChargePrefix.prover P)) Q
    (by rw [htr]; exact hQ) (by rw [htr]; exact hout) n hlo hhi a hfirst Wd
    (by rw [htr]; exact hw)
  rw [htr] at hb
  obtain ⟨own, pend, g, hd, hf⟩ := hb
  -- the dispatch row of row n's frame
  have hrow : AspisRows40.Starts.finalRow a = some n := by
    have hc := AspisRec40.FinalLegacy.chain_firstCell_eq40 D H
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 hv40 n hhi
    rw [AspisRec40.FinalLegacy.legacy_firstCell _ _ _ n (by omega) (by omega) (by omega),
      hfirst] at hc
    have hae := Option.some.inj hc
    rw [hae]
    unfold UnifiedSteps.address
    rw [AspisRows40.Starts.finalRow_absorb _ n hhi, if_pos hlo]
  refine ⟨own, pend, g, ?_, ?_⟩
  · unfold AspisRows40.FinalStarts.decFinal
    rw [AspisRows40.Starts.decAspis_final _ _ _ n hrow]
    exact hd
  · rw [hf]
    apply congrArg some
    rw [AspisRows40.Protocol.transcript_eq D _ H _ (RawCutTranscriptRun.proof Wd _) n,
      RawCutTranscriptRun.transcript_eq, AspisRows40.Protocol.transcript_eq]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    unfold FS2.Protocol.chal
    rw [AspisRows40.Protocol.chain_eq, AspisRows40.Protocol.chain_eq, RawCutTranscriptRun.chain_eq]

#print axioms final_decodes

end AspisRec40.FinalDecoding
end
