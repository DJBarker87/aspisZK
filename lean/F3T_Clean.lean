import F3T_AcceptedFacts
import F3T_Completion
import F3T_Accounting
import OraclePortHeadline
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.F3T_Clean
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open F3T_Experiment F3T_Charged F3T_Canon F3T_Prefix F3T_Causal F3T_AcceptedFacts
open RawRecordedOracleExtractionMassBin
attribute [local irreducible] R0C.V3.hitsChain3 GenericNoHit.hitFrom LiteralClassifier.bad
abbrev prefixHit (D : LiteralByteProtocol.Decoder) (P : Prover)
    (run : RawCutProverCompiler.RunView) : Prop :=
  hitsChain3 RecordedBinaryExperimentBin.dec RawAdaptiveClassifierHitDensity.classifier
    emptyTable (recovered D (canon P) run).1

def bad (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (run : RawCutProverCompiler.RunView) : Prop :=
  RecordedBinaryExperimentBin.binaryCollision (Q+1161) run ∨ prefixHit D P run

/-- The original extractor failure event is clean outside full-log collisions
and prefix-only classifier hits. The desired probability bound is not a premise. -/
theorem clean (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    CleanAcceptedModel D (projected D (canon P)) (bad D P Q) := by
  intro H run ha hn
  have hc : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161) run :=
    fun h => hn (Or.inl h)
  have hh : ¬ prefixHit D P run := fun h => hn (Or.inr h)
  obtain ⟨checks,fixed,tag⟩ := accepted_facts D P Q hq H hc ha
  have format := RWireCheckedFormat.format_of_checks D H _ _ checks
  rw [same_transcript D (canon P) H,charged_eval] at format
  have fmt : RWireCheckedFormat.Format (eval H (base D (canon P))).2.1.2 :=
    RWireCheckedFormat.format_of_enrich _ _ format
  obtain ⟨tail,htail⟩ := chronological_prefix D (canon P) H
  have fullReads := F3T_Accounting.first_reads D P Q hq H
  have hQ : firstReads emptyTable (eval H (base D (canon P))).1 ≤ Q+1161 := by
    have h := TraceAppend.firstReads_le_append emptyTable (eval H (charged D (canon P))).1 tail
    rw [← htail] at h
    rw [charged_eval] at h
    exact h.trans fullReads
  have hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1161)) emptyTable (eval H (base D (canon P))).1 := by
    intro h
    apply hc
    change hitsBad _ emptyTable (eval H (projected D (canon P))).1
    rw [htail,charged_eval]
    exact TraceAppend.hitsBad_of_prefix _ _ _ _ h
  have hd := F3T_Completion.decodes D (canon P) H (Q+1161) hQ hout fmt tag
  refine ⟨?_,?_⟩
  · rw [fixed]; exact checks
  · rw [fixed]
    intro hit
    have hit' : GenericNoHit.hitFrom LiteralClassifier.bad (eval H (charged D (canon P))).2.1.1 []
        ((LiteralByteProtocol.protocol D).transcript H (eval H (charged D (canon P))).2.1.1
          (eval H (charged D (canon P))).2.1.2 33).rounds := by
      rw [← same_transcript D (canon P) H]
      exact hit
    apply hh
    change hitsChain3 _ _ _ (recovered D (canon P) (eval H (projected D (canon P)))).1
    rw [recovered_eval]
    exact F3T_Completion.hit_in_prefix D (canon P) H hd hit'

#print axioms clean
end AspisR1.F3T_Clean
end
