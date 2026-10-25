import OraclePortFrozen2Bounds

/-! Unadopted option B prototype. The physical carrier is never substituted
for semantic initialization. Source provenance is a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3_Model
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable

structure PhysicalPublic where
  bytes : Bytes

structure SemanticPublic where
  value : LiteralTranscript.Public

structure Input where
  semantic : SemanticPublic
  physical : PhysicalPublic
  proof : RawCutProverCompiler.Proof
  stored : Bytes

def checkpoint (physical : PhysicalPublic) (stored : Bytes) (p : Parsed)
    (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (v : LiteralOpeningView.View) :=
  OraclePortCheckpointOracleC5.writeResume stored physical.bytes
    (OraclePortAcceptedContextC6.context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q

def afterBatch0 (physical : PhysicalPublic) (stored : Bytes) (p : Parsed)
    (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) : Program Bytes State Bool :=
  match input p q tr, LiteralOpeningView.read (typedRows p q tr) with
  | some i, some v => bind (checkpoint physical stored p q tr i v) fun resumed =>
      match resumed with
      | none => .done false
      | some a => OraclePortFrozen2.stage2 p q tr i a
  | _, _ => .done false

def decision (physical : PhysicalPublic) : OraclePortStoredExperimentC4.Decision := fun stored tr _ =>
  if OraclePortAdmission.Guard tr then
    match OraclePortStoredParserC4.parseReached stored tr, queries tr with
    | some p, some q => bind (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0) fun ok =>
        if ok then afterBatch0 physical stored p q tr else .done false
    | _, _ => .done false
  else .done false

/-- The actual complete interface: all 33 sampler rows, including the complete
8-pair query chain, precede decision. This is not bare terminal dV. -/
def verifier (D : LiteralByteProtocol.Decoder) (i : Input) : Program Bytes State Bool :=
  OraclePortStoredExperimentC4.verifier D (decision i.physical)
    ⟨i.semantic.value,i.proof,i.stored⟩

theorem checkpoint_value (H : Bytes → State) (physical : PhysicalPublic)
    (stored : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (v : LiteralOpeningView.View) :
    (eval H (checkpoint physical stored p q tr i v)).2 =
      some (OraclePortFrozen2.completeState i q) :=
  OraclePortCheckpointOracleC5.writeResume_value H stored physical.bytes _ _ _ q

theorem checkpoint_reads (H : Bytes → State) (physical : PhysicalPublic)
    (stored : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (v : LiteralOpeningView.View) :
    (eval H (checkpoint physical stored p q tr i v)).1.length = 6 :=
  OraclePortCheckpointOracleC5.writeResume_reads H stored physical.bytes _ _ _ q

/-- Retains the entire sampler log verbatim. In particular the unused query
scan suffix is not deleted or replaced by a short-circuiting sampler. -/
theorem complete_schedule (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : Input) :
    eval H (verifier D i) =
      let tr := (LiteralByteProtocol.protocol D).transcript H i.semantic.value i.proof 33
      let terminal := eval H (OracleDecisionFeasibilityCore.onBytes
        (decision i.physical i.stored) tr (i.proof 33))
      ((((List.range 33).map fun j => (eval H
        ((LiteralByteProtocol.protocol D).chain H i.semantic.value i.proof j).toProgram).1).flatten
        ++ terminal.1),terminal.2) :=
  OracleDecisionFeasibilityBudget.verifier_eval D (decision i.physical i.stored) H _ _

#print axioms checkpoint_value
#print axioms checkpoint_reads
#print axioms complete_schedule
end AspisR1.F3_Model
end
