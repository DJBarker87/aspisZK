import F3T_Charged
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Prefix
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open F3T_Experiment F3T_Charged
open F3T_Projection (project)

theorem same_transcript (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (projected D P)).2.1=(eval H (charged D P)).2.1 := by
  rw [projected_eval,F3T_Projection.recorded_view]
  rw [OracleDecisionPrereqStarts.annotated,
    OracleDecisionFeasibilityCompiler.compiled_experiment_eval,charged_eval]
  dsimp only
  change ((eval H (OraclePortExperiment.original D
    (F3_Model.decision (eval H P).2.physical (eval H P).2.stored) (project P))).2.1.1,
    RawCutTranscriptRun.proof (build D (eval H (OraclePortExperiment.original D
      (F3_Model.decision (eval H P).2.physical (eval H P).2.stored) (project P))))
      (eval H (OraclePortExperiment.original D
        (F3_Model.decision (eval H P).2.physical (eval H P).2.stored) (project P))).2.1.2)=_
  rw [OraclePortSamplerPrefixDraft.words_prefix,OraclePortSamplerPrefixDraft.output_pair]

theorem chronological_prefix (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    ∃ tail,(eval H (projected D P)).1=(eval H (charged D P)).1 ++ tail := by
  rw [projected_eval,F3T_Projection.recorded_view]
  rw [OracleDecisionPrereqStarts.annotated,
    OracleDecisionFeasibilityCompiler.compiled_experiment_eval,charged_eval]
  dsimp only
  change ∃ tail,(eval H (OraclePortExperiment.original D
    (F3_Model.decision (eval H P).2.physical (eval H P).2.stored) (project P))).1 ++ _=
      (eval H (base D P)).1 ++ tail
  rw [OraclePortSamplerPrefixDraft.split_trace,List.append_assoc]
  exact ⟨_,rfl⟩

theorem first_start_before_terminal (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) (a : Bytes) (read : Read (eval H (charged D P)).1 a) :
    firstIdx a (eval H (projected D P)).1=firstIdx a (eval H (charged D P)).1 := by
  obtain ⟨tail,equal⟩ := chronological_prefix D P H
  rw [equal]
  exact OracleProgramRecording.firstIdx_append_of_read a _ tail read

#print axioms same_transcript
#print axioms chronological_prefix
#print axioms first_start_before_terminal
end AspisR1.F3T_Prefix
end
