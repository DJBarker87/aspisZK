import OraclePortStoredAdmissionC4
import OraclePortStoredProjectionC4
import BinCompiledRunWordStability
import AspisRec40Compiler
import AspisRows40FinalStarts

/-! Aspis 40-row recorded experiment: the charged experiment and its start
count, copy of the charged part of R1's `Frozen2StartChargePrefix`
(`prover`, `base`, `charged`, `charged_eval`, `prover_eval`, `starts`).

Replaced: R1's 33-row verifier by `AspisRows40.Starts.verifier`, R1's compiler
by `AspisRec40.Compiler.compiled`, R1's byte decoder
`RecordedBinaryExperimentBin.dec` by the Aspis decoder
`AspisRows40.FinalStarts.decFinal`, and R1's verifier count 34 by 41
(`FinalStarts.verifier_starts`). Reused unchanged: the stored-input prover type
`OraclePortStoredExperimentC4.Prover`, its canonicalisation and projection
(`OraclePortStoredAdmissionC4.canon`, `OraclePortStoredProjectionC4.project`),
the word builder `BinCompiledRunWordStability.wordsFromRun D` (it reads rows
0, 2 and 30 of `LiteralByteProtocol.protocol D`'s chains, which equal the
40-row protocol's chains, `Protocol.chain_eq`), the experiment type
`RawRecordedOracleExtractionMassBin.Experiment`, and the generic count
`DecoderQueryAccounting.starts_le_queries`.

Not copied here: R1's `same_transcript`, `chronological_prefix`,
`first_start_before_terminal`, `transcript_start_read` and `recovered`, which
relate the charged experiment to R1's full experiment `projected D P` (built
with R1's two-transaction decision `OraclePortFrozen2.dV_frozen2`). Their
Aspis forms need the Aspis full experiment; see RECORDED-EXPERIMENT-40.md. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.ChargePrefix
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4

/-- R1's `Frozen2StartChargePrefix.prover`, unchanged (generic in the protocol). -/
abbrev prover (P : Prover) := OraclePortStoredProjectionC4.project (canon P)

/-- Copy of `Frozen2StartChargePrefix.base`. -/
abbrev base (D : LiteralByteProtocol.Decoder) (P : Prover) :=
  RawCutProverCompiler.experiment (prover P) (AspisRows40.Starts.verifier D (fun _ _ => true))

/-- Copy of `Frozen2StartChargePrefix.charged`. -/
def charged (D : LiteralByteProtocol.Decoder) (P : Prover) :
    RawRecordedOracleExtractionMassBin.Experiment :=
  bind (Compiler.compiled D (fun _ _ => true)
    (BinCompiledRunWordStability.wordsFromRun D) (prover P)) fun i => .done (i,true)

/-- Copy of `Frozen2StartChargePrefix.charged_eval`. -/
theorem charged_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    eval H (charged D P) =
      ((eval H (base D P)).1,
        (((eval H (base D P)).2.1.1, RawCutTranscriptRun.proof
          (BinCompiledRunWordStability.wordsFromRun D (eval H (base D P)))
          (eval H (base D P)).2.1.2),true)) := by
  simp only [charged,eval_bind,Compiler.eval_compiled,eval,List.append_nil,base]

/-- Copy of `Frozen2StartChargePrefix.prover_eval` (same proof). -/
theorem prover_eval (P : Prover) (H : Bytes → State) :
    eval H (prover P) = ((eval H P).1,
      ((eval H P).2.statement,R16CanonReduction.proof (eval H P).2.proof)) := by
  rw [prover,OraclePortStoredProjectionC4.project_eval,canon_eval]
  rfl

/-- Copy of `Frozen2StartChargePrefix.starts`: `Q + 34` becomes `Q + 41`. -/
theorem starts (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads AspisRows40.FinalStarts.decFinal emptyTable
      (eval H (charged D P)).1 ≤ Q+41 := by
  rw [charged_eval]
  unfold base
  rw [RawCutProverCompiler.experiment_eval,
    DecodedFirstReadUnionBound.decoderFirstReads_append]
  have hp := DecoderQueryAccounting.starts_le_queries AspisRows40.FinalStarts.decFinal
    emptyTable (eval H (prover P)).1
  have hlen : (eval H (prover P)).1.length ≤ Q := by rw [prover_eval]; exact hq H
  exact Nat.add_le_add (hp.trans hlen) (AspisRows40.FinalStarts.verifier_starts D
    (fun _ _ => true) H _ _ _)

#print axioms charged_eval
#print axioms prover_eval
#print axioms starts

end AspisRec40.ChargePrefix
end
