import OraclePortStoredExperimentC4
import OraclePortChecks

/-! R16 admission and typed-check composition for the additional stored-proof
input. No acceptance-to-arithmetic implication is assumed to be established
for the multiproof-only kernel. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredAdmissionC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable

abbrev build (D : LiteralByteProtocol.Decoder) := BinCompiledRunWordStability.wordsFromRun D
abbrev annotated (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) :=
  recorded D d (build D) P
abbrev output (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) := (eval H (annotated D d P)).2.1
abbrev rows (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) := ((LiteralByteProtocol.protocol D).transcript H
      (output D d P H).statement (output D d P H).proof 33).rounds

def admitted (d : Decision) : Decision := fun stored => OraclePortAdmission.admit (d stored)
def canonInput (i : Input) : Input := {i with proof := R16CanonReduction.proof i.proof}
def canon (P : Prover) : Prover := bind P fun i => .done (canonInput i)

theorem canon_eval (P : Prover) (H : Bytes → State) :
    eval H (canon P) = ((eval H P).1,canonInput (eval H P).2) := by
  simp only [canon,eval_bind,eval,List.append_nil]

theorem canon_acceptance (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    (eval H (original D d (canon P))).2.2 = (eval H (original D d P)).2.2 := by
  rw [original_eval,canon_eval,original_eval]
  change (eval H (OraclePortExperiment.verifier D (d (eval H P).2.stored)
    (eval H P).2.statement (R16CanonReduction.proof (eval H P).2.proof))).2 = _
  exact congrArg (fun program => (eval H program).2)
    (OraclePortCanon.verifier_congr D (d (eval H P).2.stored)
      (eval H P).2.statement (eval H P).2.proof
      (R16CanonReduction.proof (eval H P).2.proof) (R16CanonReduction.erase_proof _))

def InstanceFields (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) (i : SourceInputs) : Prop :=
  SemanticPublicWire.parsePublic (output D d P H).statement.pubBytes = some i.decoded ∧
  (rows D d P H)[31]? = some (i.m31,
    (TranscriptView.Value.queries (.ok i.queryBytes),i.state31)) ∧
  (rows D d P H)[32]? = some (i.m32,
    (TranscriptView.Value.ordinary i.rho,i.state32)) ∧
  LiteralTranscript.valid 31 i.m31 ∧ LiteralTranscript.valid 32 i.m32

theorem accepted_guard (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State)
    (ha : (eval H (original D (admitted d) P)).2.2 = true) :
    OraclePortAdmission.Guard (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H (eval H P).2.statement
        (eval H P).2.proof 33)) := by
  rw [original_eval] at ha
  change (eval H (OraclePortExperiment.verifier D _ _ _)).2 = true at ha
  rw [OracleDecisionFeasibilityBudget.verifier_eval] at ha
  exact OraclePortAdmission.accepted_guard _ H _ _ ha

theorem compiled_erasure (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
      (output D d P H).statement (output D d P H).proof 33) =
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
      (eval H P).2.statement (eval H P).2.proof 33) := by
  unfold output annotated
  rw [recorded_eval,original_eval]
  change LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
      (eval H P).2.statement (RawCutTranscriptRun.proof _ (eval H P).2.proof) 33) = _
  rw [RawCutTranscriptRun.transcript_eq,CanonicalCutEnrichedTranscript.erasePrefix_enrich]

theorem fields_to_instance (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (fields : D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H (output D d P H).statement
        (output D d P H).proof 33)) i)
    (v31 : LiteralTranscript.valid 31 ((output D d P H).proof 31))
    (v32 : LiteralTranscript.valid 32 ((output D d P H).proof 32)) :
    InstanceFields D d P H i := by
  have at31 := LiteralByteRunFacts.transcript_index D H (output D d P H).statement
    (output D d P H).proof 33 31 (by decide)
  have at32 := LiteralByteRunFacts.transcript_index D H (output D d P H).statement
    (output D d P H).proof 33 32 (by decide)
  have e31 := fields.2.1
  have e32 := fields.2.2.1
  simp only [LiteralTranscript.erasePrefix,List.getElem?_map,at31,at32,
    Option.map_some,Option.some.injEq] at e31 e32
  have m31 := D0InstanceAdmission.valid_payload_injective 31 (by decide) (by decide) (by decide)
    _ i.m31 v31 fields.2.2.2.1 (congrArg Prod.fst e31)
  have m32 := D0InstanceAdmission.valid_payload_injective 32 (by decide) (by decide) (by decide)
    _ i.m32 v32 fields.2.2.2.2 (congrArg Prod.fst e32)
  exact ⟨fields.1,at31.trans (congrArg some (Prod.ext m31
      (congrArg (fun x : RawCutTranscriptRun.ErasedMessage × LiteralTranscript.Challenge => x.2) e31))),
    at32.trans (congrArg some (Prod.ext m32
      (congrArg (fun x : RawCutTranscriptRun.ErasedMessage × LiteralTranscript.Challenge => x.2) e32))),
    fields.2.2.2⟩

theorem accepted_instance (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State)
    (ha : (eval H (original D (admitted d) (canon P))).2.2 = true) :
    ∃ i : SourceInputs, InstanceFields D (admitted d) (canon P) H i := by
  have accepted : (eval H (original D (admitted d) P)).2.2 = true := by
    rw [← canon_acceptance]; exact ha
  have guard := accepted_guard D d P H accepted
  obtain ⟨i,fields⟩ := guard.2.2
  have shape := D0ScheduleAdmission.shape_of_schedule D H
    (eval H P).2.statement (eval H P).2.proof guard.2.1
  have he := compiled_erasure D (admitted d) (canon P) H
  rw [canon_eval] at he
  have same := R16DecisionErasure.erased_transcript_eq D H
    (eval H P).2.statement (eval H P).2.proof
    (R16CanonReduction.proof (eval H P).2.proof) (R16CanonReduction.erase_proof _) 33
  have fields' : D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H
        (output D (admitted d) (canon P) H).statement
        (output D (admitted d) (canon P) H).proof 33)) i := by
    rw [he]
    change D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H (eval H P).2.statement
        (R16CanonReduction.proof (eval H P).2.proof) 33)) i
    rw [same]
    exact fields
  have valid (row : Nat) (hr : row < 33) :
      LiteralTranscript.valid row ((output D (admitted d) (canon P) H).proof row) := by
    unfold output annotated
    rw [recorded_eval,original_eval,canon_eval]
    apply D0ScheduleAdmission.enrich_valid
    exact R16CanonReduction.valid_of_shape _ shape row hr
  exact ⟨i,fields_to_instance D _ _ H i fields' (valid 31 (by decide)) (valid 32 (by decide))⟩

#print axioms canon_eval
#print axioms canon_acceptance
#print axioms accepted_guard
#print axioms compiled_erasure
#print axioms fields_to_instance
#print axioms accepted_instance
end AspisR1.OraclePortStoredAdmissionC4
end
