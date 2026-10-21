import OraclePortCanon
import D0InstanceAdmission
import InitialTagDecision

/-! Model admission only: public parsing, late-row placement, erased schedule
and public tag. It deliberately does not identify wire proof length/magic
or the Rust public tag with this Public carrier. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortAdmission
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler (Public Proof Prover RunView experiment)
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open OraclePortExperiment (Decision verifier original recorded)
open OracleDecisionFeasibilityCompiler (compiled_experiment_eval)
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable

abbrev annotatedRun (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (H : Bytes → State) := eval H (recorded D dO P)
abbrev compiledPublic (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (H : Bytes → State) := (annotatedRun D dO P H).2.1.1
abbrev compiledRows (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (H : Bytes → State) := ((LiteralByteProtocol.protocol D).transcript H
      (compiledPublic D dO P H) (annotatedRun D dO P H).2.1.2 33).rounds

def InstanceFields (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (H : Bytes → State) (i : SourceInputs) : Prop :=
  SemanticPublicWire.parsePublic (compiledPublic D dO P H).pubBytes = some i.decoded ∧
  (compiledRows D dO P H)[31]? = some (i.m31,
    (TranscriptView.Value.queries (.ok i.queryBytes), i.state31)) ∧
  (compiledRows D dO P H)[32]? = some (i.m32,
    (TranscriptView.Value.ordinary i.rho, i.state32)) ∧
  LiteralTranscript.valid 31 i.m31 ∧ LiteralTranscript.valid 32 i.m32

def Guard (p : ErasedPrefix) : Prop :=
  p.statement.tag = 2 ∧ D0ScheduleAdmission.Schedule p ∧ ∃ i, D0InstanceAdmission.Fields p i

def admit (core : Decision) : Decision := fun p m =>
  if Guard p then core p m else .done false

theorem accepted_guard (core : Decision) (H : Bytes → State)
    (p : ErasedPrefix) (m : ErasedMessage)
    (ha : (eval H (admit core p m)).2 = true) : Guard p := by
  by_cases hg : Guard p
  · exact hg
  · simp only [admit, if_neg hg, eval, Bool.false_eq_true] at ha

theorem admission_budget (core : Decision) (hb : OraclePortExperiment.Budget core) :
    OraclePortExperiment.Budget (admit core) := by
  intro H p m
  by_cases hg : Guard p
  · simpa only [admit, if_pos hg] using hb H p m
  · simp only [admit, if_neg hg, eval, List.length_nil]; omega

theorem accepted_terminal (D : LiteralByteProtocol.Decoder) (core : Decision)
    (P : Prover) (H : Bytes → State)
    (ha : FS2.accepts (eval H (original D (admit core) P))) :
    Guard (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
      (eval H P).2.1 (eval H P).2.2 33)) := by
  apply accepted_guard core H _ (LiteralTranscript.erase ((eval H P).2.2 33))
  change (eval H (original D (admit core) P)).2.2 = true at ha
  rw [original, OracleDecisionFeasibilityCore.original, RawCutProverCompiler.experiment_eval,
    OracleDecisionFeasibilityBudget.verifier_eval] at ha
  exact ha

theorem accepted_tag (D : LiteralByteProtocol.Decoder) (core : Decision)
    (P : Prover) (H : Bytes → State)
    (ha : FS2.accepts (eval H (original D (admit core) P))) :
    (eval H (original D (admit core) P)).2.1.1.tag = 2 := by
  have hg := (accepted_terminal D core P H ha).1
  rw [InitialTagDecision.erased_transcript_tag] at hg
  rw [original, OracleDecisionFeasibilityCore.original, RawCutProverCompiler.experiment_eval]
  exact hg

/-- No decision assumption is needed to transport a parsed erased witness to
R16 once the two compiled constructors have been identified. -/
theorem fields_to_instance (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State)
    (i : SourceInputs)
    (h : D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H (compiledPublic D d P H)
        (annotatedRun D d P H).2.1.2 33)) i)
    (v31 : LiteralTranscript.valid 31 ((annotatedRun D d P H).2.1.2 31))
    (v32 : LiteralTranscript.valid 32 ((annotatedRun D d P H).2.1.2 32)) :
    InstanceFields D d P H i := by
  let pub := compiledPublic D d P H
  let pf := (annotatedRun D d P H).2.1.2
  have at31 := LiteralByteRunFacts.transcript_index D H (compiledPublic D d P H)
    (annotatedRun D d P H).2.1.2 33 31 (by decide)
  have at32 := LiteralByteRunFacts.transcript_index D H (compiledPublic D d P H)
    (annotatedRun D d P H).2.1.2 33 32 (by decide)
  have e31 := h.2.1
  have e32 := h.2.2.1
  simp only [LiteralTranscript.erasePrefix, List.getElem?_map, at31, at32,
    Option.map_some, Option.some.injEq] at e31 e32
  have m31 := D0InstanceAdmission.valid_payload_injective 31 (by decide) (by decide) (by decide)
    (pf 31) i.m31 v31 h.2.2.2.1 (congrArg Prod.fst e31)
  have m32 := D0InstanceAdmission.valid_payload_injective 32 (by decide) (by decide) (by decide)
    (pf 32) i.m32 v32 h.2.2.2.2 (congrArg Prod.fst e32)
  exact ⟨h.1, at31.trans (congrArg some (Prod.ext m31 (congrArg (fun x : ErasedMessage × LiteralTranscript.Challenge => x.2) e31))),
    at32.trans (congrArg some (Prod.ext m32 (congrArg (fun x : ErasedMessage × LiteralTranscript.Challenge => x.2) e32))), h.2.2.2.1, h.2.2.2.2⟩

theorem compiled_erasure (D : LiteralByteProtocol.Decoder)
    (dO : Decision) (P : Prover) (H : Bytes → State) :
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
      (compiledPublic D dO P H) (annotatedRun D dO P H).2.1.2 33) =
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
      (eval H P).2.1 (eval H P).2.2 33) := by
  unfold compiledPublic annotatedRun recorded OracleDecisionPrereqStarts.annotated
  rw [compiled_experiment_eval]
  dsimp only
  rw [RawCutTranscriptRun.transcript_eq,
    CanonicalCutEnrichedTranscript.erasePrefix_enrich]
  rw [RawCutProverCompiler.experiment_eval]

theorem accepted_instance (D : LiteralByteProtocol.Decoder) (core : Decision)
    (P : Prover) (H : Bytes → State)
    (ha : FS2.accepts (eval H (original D (admit core) P))) :
    ∃ i : SourceInputs, InstanceFields D (admit core) (R16CanonReduction.canon P) H i := by
  have hg := accepted_terminal D core P H ha
  obtain ⟨i, fields⟩ := hg.2.2
  have shape := D0ScheduleAdmission.shape_of_schedule D H
    (eval H P).2.1 (eval H P).2.2 hg.2.1
  have he := compiled_erasure D (admit core) (R16CanonReduction.canon P) H
  rw [R16CanonReduction.eval_canon] at he
  dsimp only at he
  have hs := R16DecisionErasure.erased_transcript_eq D H (eval H P).2.1 (eval H P).2.2
    (R16CanonReduction.proof (eval H P).2.2) (R16CanonReduction.erase_proof _) 33
  have hf : D0InstanceAdmission.Fields
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
        (compiledPublic D (admit core) (R16CanonReduction.canon P) H)
        (annotatedRun D (admit core) (R16CanonReduction.canon P) H).2.1.2 33)) i := by
    rw [he, hs]
    exact fields
  have hv (row : Nat) (hr : row < 33) : LiteralTranscript.valid row
      ((annotatedRun D (admit core) (R16CanonReduction.canon P) H).2.1.2 row) := by
    unfold annotatedRun recorded OracleDecisionPrereqStarts.annotated
    rw [compiled_experiment_eval]
    apply D0ScheduleAdmission.enrich_valid
    rw [RawCutProverCompiler.experiment_eval, R16CanonReduction.eval_canon]
    exact R16CanonReduction.valid_of_shape _ shape row hr
  exact ⟨i, fields_to_instance D (admit core) (R16CanonReduction.canon P) H i hf
    (hv 31 (by decide)) (hv 32 (by decide))⟩

def source (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover)
    (fallback : (Bytes → State) → SourceInputs) (H : Bytes → State) : SourceInputs :=
  if h : ∃ i : SourceInputs, InstanceFields D (admit core) (R16CanonReduction.canon P) H i
  then Classical.choose h else fallback H

theorem h_R16_instance (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover)
    (fallback : (Bytes → State) → SourceInputs) (H : Bytes → State)
    (ha : FS2.accepts (eval H (original D (admit core) (R16CanonReduction.canon P)))) :
    InstanceFields D (admit core) (R16CanonReduction.canon P) H
      (source D core P fallback H) := by
  have ha' : FS2.accepts (eval H (original D (admit core) P)) := by
    change (eval H (original D (admit core) (R16CanonReduction.canon P))).2.2 = true at ha
    rw [OraclePortCanon.original_canon] at ha
    exact ha
  have hx := accepted_instance D core P H ha'
  simp only [source, dif_pos hx]
  exact Classical.choose_spec hx

#print axioms accepted_guard
#print axioms admission_budget
#print axioms accepted_terminal
#print axioms accepted_tag
#print axioms fields_to_instance
#print axioms compiled_erasure
#print axioms accepted_instance
#print axioms h_R16_instance
end AspisR1.OraclePortAdmission
end
