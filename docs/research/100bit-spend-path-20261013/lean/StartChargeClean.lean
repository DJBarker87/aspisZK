import StartChargeCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.StartChargeClean
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open OraclePortFrozenOrderConsumer StartChargePrefix
open RawRecordedOracleExtractionMassBin
attribute [local irreducible] R0C.V3.hitsChain3 GenericNoHit.hitFrom LiteralClassifier.bad

/-- All checks and word alignment are inherited at the full accepted run;
no decision on a fixed stored fibre is used under a probability law. -/
theorem accepted_facts (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State)
    (hc : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161) (eval H (projected D P)))
    (ha : (eval H (projected D P)).2.2 = true) :
    ∃ checks : LiteralAcceptanceTerminal.Checks (eval H (projected D P)).2.1.1
        ((LiteralByteProtocol.protocol D).transcript H (eval H (projected D P)).2.1.1
          (eval H (projected D P)).2.1.2 33).rounds,
      RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun
        (eval H (projected D P))) (eval H (projected D P)).2.1.2 =
        (eval H (projected D P)).2.1.2 ∧
      (eval H (base D P)).2.1.1.tag = 2 := by
  let s := (eval H P).2.stored
  let d := dV s
  have same : eval H (projected D P) =
      eval H (OraclePortExperiment.recorded D d (prover P)) := by
    rw [projected_eval,OraclePortStoredReductionC7.annotated_selected,fibre_prover]
  have hcf : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
      (eval H (OraclePortExperiment.recorded D d (prover P))) := by rw [← same]; exact hc
  have haf : (eval H (OraclePortExperiment.original D d (prover P))).2.2 = true := by
    rw [same] at ha
    change (eval H (OracleDecisionPrereqStarts.annotated D d _ (prover P))).2.2 = true at ha
    rw [OracleDecisionPrereqStarts.annotated,
      OracleDecisionFeasibilityCompiler.compiled_experiment_eval] at ha
    exact ha
  have cf := fibre_checks D s P Q hq
  change OraclePortConsumer.CheckedAcceptance D d
    (OraclePortStoredReductionC7.pairProver s P) (Q+1161) at cf
  rw [fibre_prover] at cf
  have checks := cf H hcf haf
  have fixed := (OraclePortCleanModel.extractor_word_alignment D d (prover P) H checks).2
  have tag : (eval H (OraclePortExperiment.original D d (prover P))).2.1.1.tag = 2 := by
    change (eval H (OraclePortExperiment.original D (dV s) (prover P))).2.1.1.tag = 2
    change (eval H (OraclePortExperiment.original D (dV s) (prover P))).2.2 = true at haf
    rw [← admitted_dV s] at haf ⊢
    exact OraclePortAdmission.accepted_tag D (dV s) (prover P) H haf
  rw [OraclePortSamplerPrefixDraft.output_pair] at tag
  refine ⟨?_,?_,tag⟩
  · rw [same]; exact checks
  · rw [same]; exact fixed

abbrev prefixHit (D : LiteralByteProtocol.Decoder) (P : Prover)
    (run : RawCutProverCompiler.RunView) : Prop :=
  hitsChain3 RecordedBinaryExperimentBin.dec RawAdaptiveClassifierHitDensity.classifier
    emptyTable (recovered D P run).1

def bad (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (run : RawCutProverCompiler.RunView) : Prop :=
  RecordedBinaryExperimentBin.binaryCollision (Q+1161) run ∨ prefixHit D P run

/-- The original extractor failure event is clean outside full-log collisions
and prefix-only classifier hits. The desired probability bound is not a premise. -/
theorem clean (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    CleanAcceptedModel D (projected D P) (bad D P Q) := by
  intro H run ha hn
  have hc : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161) run :=
    fun h => hn (Or.inl h)
  have hh : ¬ prefixHit D P run := fun h => hn (Or.inr h)
  obtain ⟨checks,fixed,tag⟩ := accepted_facts D P Q hq H hc ha
  have format := RWireCheckedFormat.format_of_checks D H _ _ checks
  rw [same_transcript D P H,charged_eval] at format
  have fmt : RWireCheckedFormat.Format (eval H (base D P)).2.1.2 :=
    RWireCheckedFormat.format_of_enrich _ _ format
  obtain ⟨tail,htail⟩ := chronological_prefix D P H
  have fullReads := OraclePortFrozenOrderProbability.first_reads D P Q hq H
  have hQ : firstReads emptyTable (eval H (base D P)).1 ≤ Q+1161 := by
    have h := TraceAppend.firstReads_le_append emptyTable (eval H (charged D P)).1 tail
    rw [← htail] at h
    rw [charged_eval] at h
    exact h.trans fullReads
  have hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1161)) emptyTable (eval H (base D P)).1 := by
    intro h
    apply hc
    change hitsBad _ emptyTable (eval H (projected D P)).1
    rw [htail,charged_eval]
    exact TraceAppend.hitsBad_of_prefix _ _ _ _ h
  have hd := StartChargeCompletion.decodes D P H (Q+1161) hQ hout fmt tag
  refine ⟨?_,?_⟩
  · rw [fixed]; exact checks
  · rw [fixed]
    intro hit
    have hit' : GenericNoHit.hitFrom LiteralClassifier.bad (eval H (charged D P)).2.1.1 []
        ((LiteralByteProtocol.protocol D).transcript H (eval H (charged D P)).2.1.1
          (eval H (charged D P)).2.1.2 33).rounds := by
      rw [← same_transcript D P H]
      exact hit
    apply hh
    change hitsChain3 _ _ _ (recovered D P (eval H (projected D P))).1
    rw [recovered_eval]
    exact StartChargeCompletion.hit_in_prefix D P H hd hit'

#print axioms accepted_facts
#print axioms clean
end AspisR1.StartChargeClean
end
