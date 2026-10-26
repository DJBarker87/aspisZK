import F3T_Projection
import Frozen2StartChargePrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Charged
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Experiment
open F3T_Projection (project)

abbrev build (D : LiteralByteProtocol.Decoder) := BinCompiledRunWordStability.wordsFromRun D
abbrev base (D : LiteralByteProtocol.Decoder) (P : Prover) :=
  RawCutProverCompiler.experiment (project P) (RawCutProverCompiler.verifier D (fun _ _ => true))

def charged (D : LiteralByteProtocol.Decoder) (P : Prover) :
    RawRecordedOracleExtractionMassBin.Experiment :=
  bind (RawCutProverCompiler.compiled D (fun _ _ => true) (build D) (project P))
    fun i => .done (i,true)

def projected (D : LiteralByteProtocol.Decoder) (P : Prover) :
    RawRecordedOracleExtractionMassBin.Experiment :=
  bind (recorded D (build D) P) fun r => .done ((r.1.semantic.value,r.1.proof),r.2)

theorem charged_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    eval H (charged D P)=
      ((eval H (base D P)).1,
        (((eval H (base D P)).2.1.1,RawCutTranscriptRun.proof
          (build D (eval H (base D P))) (eval H (base D P)).2.1.2),true)) := by
  simp only [charged,eval_bind,RawCutProverCompiler.eval_compiled,eval,List.append_nil,base]

theorem projected_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    eval H (projected D P)=view (eval H (recorded D (build D) P)) := by
  simp only [projected,eval_bind,eval,List.append_nil,view]

theorem starts (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (charged D P)).1≤Q+34 := by
  rw [charged_eval]
  unfold base
  rw [RawCutProverCompiler.experiment_eval,DecodedFirstReadUnionBound.decoderFirstReads_append]
  have hp := DecoderQueryAccounting.starts_le_queries RecordedBinaryExperimentBin.dec
    emptyTable (eval H (project P)).1
  have hlen : (eval H (project P)).1.length≤Q := by
    rw [F3T_Projection.project_eval];exact hq H
  exact Nat.add_le_add (hp.trans hlen) (BinHonestQueryBudget.verifier_starts D
    (fun _ _=>true) H _ _ _)

#print axioms charged_eval
#print axioms projected_eval
#print axioms starts
end AspisR1.F3T_Charged
end
