import OracleProgramLawExt
import OracleProgramReplay
import AspisRec40Decision

/-! Aspis 40-row recorded experiment: the full experiment with a terminal
decision as a PARAMETER, and the equality of its prefix-hit mass with the
charged hit mass.

Copies, for the 40-row protocol and with R1's fixed decision
`OraclePortFrozen2.dV_frozen2` replaced by a parameter `d` of exactly its type
`OraclePortStoredExperimentC4.Decision` (`Bytes → ErasedPrefix → ErasedMessage →
Program Bytes State Bool`), of:
* `OraclePortStoredExperimentC4.{verifier, original, compiled, recorded,
  original_eval, compiled_eval}` and `OraclePortStoredAdmissionC4.annotated`;
* `OraclePortFrozen2Consumer.projected` (as `projected D d P`);
* `Frozen2StartChargePrefix.{chronological_prefix, recovered, recovered_eval}`;
* `Frozen2StartChargeClean.prefixHit` and `Frozen2StartChargeProbability.hit_mass`,
  with R1's decoder `RecordedBinaryExperimentBin.dec` replaced by the Aspis
  decoder `AspisRows40.FinalStarts.decFinal`, and R1's classifier
  `RawAdaptiveClassifierHitDensity.classifier` replaced by a parameter `cls` of
  exactly its type (the Aspis classifier is another agent's).

Hypotheses on `d`: NONE. The equality holds for every decision of the type:
it uses only that the full experiment's trace begins with the charged
experiment's trace, which holds whatever the terminal decision reads. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.HitMass
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open AspisV8PairedCommitment

/-- Copy of `OraclePortStoredExperimentC4.verifier` with the 40-row verifier. -/
def verifier (D : LiteralByteProtocol.Decoder) (d : Decision) (i : Input) :
    Program Bytes State Bool :=
  AspisRec40.Decision.verifier D (d i.stored) i.statement i.proof

def original (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) :
    Program Bytes State (Input × Bool) :=
  bind P fun i => bind (verifier D d i) fun ok => .done (i,ok)

def compiled (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words) (P : Prover) :
    Prover :=
  bind (OracleProgramRecording.record (original D d P)) fun v =>
    .done (enrich (build (view v)) v.2.1)

def recorded (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words) (P : Prover) :=
  original D d (compiled D d build P)

/-- Copy of `OraclePortStoredAdmissionC4.annotated`. -/
abbrev annotated (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) :=
  recorded D d (BinCompiledRunWordStability.wordsFromRun D) P

/-- Copy of `OraclePortFrozen2Consumer.projected`, with the decision a parameter. -/
def projected (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) :
    RawRecordedOracleExtractionMassBin.Experiment :=
  bind (annotated D d (canon P)) fun v => .done ((v.1.statement,v.1.proof),v.2)

theorem original_eval (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    eval H (original D d P) =
      ((eval H P).1 ++ (eval H (verifier D d (eval H P).2)).1,
        ((eval H P).2,(eval H (verifier D d (eval H P).2)).2)) := by
  simp only [original,eval_bind,eval,List.append_nil]

theorem compiled_eval (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words)
    (P : Prover) (H : Bytes → State) :
    eval H (compiled D d build P) =
      let v := eval H (original D d P)
      (v.1,enrich (build (view v)) v.2.1) := by
  simp only [compiled,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

/-- The full trace begins with the trace of the first (recorded) run. -/
theorem projected_trace (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    ∃ tail, (eval H (projected D d P)).1 = (eval H (original D d (canon P))).1 ++ tail := by
  refine ⟨(eval H (verifier D d (eval H (compiled D d
    (BinCompiledRunWordStability.wordsFromRun D) (canon P))).2)).1, ?_⟩
  simp only [projected, annotated, recorded, eval_bind, eval, List.append_nil]
  rw [original_eval, compiled_eval]

/-- The first run's trace is the 40-row verifier's trace on R1's projected prover. -/
theorem original_canon_trace (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    (eval H (original D d (canon P))).1 =
      (eval H (AspisRec40.Decision.original D (d (eval H P).2.stored)
        (AspisRec40.ChargePrefix.prover P))).1 := by
  rw [original_eval, AspisRec40.Decision.original, RawCutProverCompiler.experiment_eval,
    AspisRec40.ChargePrefix.prover_eval, canon_eval]
  rfl

/-- Copy of `Frozen2StartChargePrefix.chronological_prefix`: all reads of the
charged experiment precede everything the terminal decision and the replay read. -/
theorem chronological_prefix (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    ∃ tail, (eval H (projected D d P)).1 = (eval H (AspisRec40.ChargePrefix.charged D P)).1 ++ tail := by
  obtain ⟨tail, ht⟩ := projected_trace D d P H
  rw [ht, original_canon_trace, AspisRec40.Decision.split_trace,
    AspisRec40.ChargePrefix.charged_eval]
  exact ⟨AspisRec40.Decision.terminal D (d (eval H P).2.stored) (AspisRec40.ChargePrefix.prover P) H
    ++ tail, by rw [List.append_assoc]⟩

/-- Copy of `Frozen2StartChargePrefix.recovered` (does not depend on `d`). -/
def recovered (D : LiteralByteProtocol.Decoder) (P : Prover)
    (run : RawCutProverCompiler.RunView) : RawCutProverCompiler.RunView :=
  eval (OracleProgramReplay.oracleOf run.1) (AspisRec40.ChargePrefix.charged D P)

/-- Copy of `Frozen2StartChargePrefix.recovered_eval`. -/
theorem recovered_eval (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :
    recovered D P (eval H (projected D d P)) = eval H (AspisRec40.ChargePrefix.charged D P) := by
  apply OracleProgramReplay.eval_oracleOf H _ _ (FS.eval_consistent H _)
  obtain ⟨tail,he⟩ := chronological_prefix D d P H
  intro a ha
  rw [he,List.map_append]
  exact List.mem_append_left _ ha

/-- The classifier type of R1's `RawAdaptiveClassifierHitDensity.classifier`. -/
abbrev Classifier := LiteralTranscript.Prefix → LiteralTranscript.Message →
  Table Bytes State → LiteralTranscript.Challenge → Prop

/-- Copy of `Frozen2StartChargeClean.prefixHit`. -/
abbrev prefixHit (cls : Classifier) (D : LiteralByteProtocol.Decoder) (P : Prover)
    (run : RawCutProverCompiler.RunView) : Prop :=
  hitsChain3 AspisRows40.FinalStarts.decFinal cls emptyTable (recovered D P run).1

/-- Copy of `Frozen2StartChargeProbability.hit_mass`, for every decision `d` and
every classifier `cls` of R1's types. -/
theorem hit_mass (cls : Classifier) (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) :
    lazyMean (projected D d P) emptyTable (fun run => indicator (prefixHit cls D P run)) =
      lazyMean (AspisRec40.ChargePrefix.charged D P) emptyTable (fun run => indicator
        (hitsChain3 AspisRows40.FinalStarts.decFinal cls emptyTable run.1)) := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  unfold prefixHit
  rw [recovered_eval]

/-- The same for any observable of the recovered charged run. -/
theorem mass_of_recovered (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (f : RawCutProverCompiler.RunView → ℚ) :
    lazyMean (projected D d P) emptyTable (fun run => f (recovered D P run)) =
      lazyMean (AspisRec40.ChargePrefix.charged D P) emptyTable f := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  rw [recovered_eval]

/-- The decision parameter has exactly R1's decision type. -/
theorem decision_type : Decision = (Bytes → OracleDecisionFeasibilityCore.Decision) := rfl

#print axioms original_eval
#print axioms compiled_eval
#print axioms projected_trace
#print axioms original_canon_trace
#print axioms chronological_prefix
#print axioms recovered_eval
#print axioms hit_mass
#print axioms mass_of_recovered
#print axioms decision_type

end AspisRec40.HitMass
end
