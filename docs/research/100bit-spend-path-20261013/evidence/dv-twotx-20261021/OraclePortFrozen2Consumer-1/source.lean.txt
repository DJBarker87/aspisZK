import OraclePortStoredReductionC7
import OraclePortFrozen2C6
import OraclePortFrozen2Bounds

/-! Reuse the inherited clean consumer on fixed fibres only pointwise.
No fixed fibre replaces the adaptive prover under lazyMean. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozen2Consumer
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortStoredReductionC7
open RawRecordedOracleExtractionMassBin
attribute [local irreducible] OraclePortStoredDecisionDraftC4.decision

abbrev dV := OraclePortFrozen2.dV_frozen2

/-- Erase only the extra stored carrier after the full adaptive computation. -/
def projected (D : LiteralByteProtocol.Decoder) (P : Prover) : Experiment :=
  bind (annotated D dV (canon P)) fun v => .done ((v.1.statement,v.1.proof),v.2)

theorem projected_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    eval H (projected D P) = view (eval H (annotated D dV (canon P))) := by
  simp only [projected,eval_bind,eval,List.append_nil,view]

abbrev bad (Q : Nat) (run : RawCutProverCompiler.RunView) : Prop :=
  RecordedBinaryExperimentBin.binaryCollision (Q+1161) run ∨
    R0C.V3.hitsChain3 RecordedBinaryExperimentBin.dec
      RawAdaptiveClassifierHitDensity.classifier emptyTable run.1

def fibre_checks (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    OraclePortConsumer.CheckedAcceptance D (dV s) (pairProver s P) (Q+1161) := by
  intro H hc ha
  have checks := OraclePortFrozen2C6.checked_acceptance D (fixStored s P) Q
    (fun H => by rw [fixStored_eval]; exact hq H) H
  have orig := original_fixed D dV s P H
  have ann := annotated_fixed D dV s P H
  have hc' : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
      (view (eval H (annotated D dV (canon (fixStored s P))))) := by
    rw [ann]; exact hc
  have ha' : (eval H (original D dV (canon (fixStored s P)))).2.2 = true :=
    (congrArg (fun v : RawCutProverCompiler.RunView => v.2.2) orig).trans ha
  have ch := checks hc' ha'
  change LiteralAcceptanceTerminal.Checks
    (view (eval H (annotated D dV (canon (fixStored s P))))).2.1.1
    ((LiteralByteProtocol.protocol D).transcript H
      (view (eval H (annotated D dV (canon (fixStored s P))))).2.1.1
      (view (eval H (annotated D dV (canon (fixStored s P))))).2.1.2 33).rounds at ch
  rw [ann] at ch
  exact ch

/-- Admission is built into dV; this is an identity of programs. -/
theorem admitted_dV (s : Bytes) : OraclePortAdmission.admit (dV s) = dV s := by
  funext tr m
  unfold OraclePortAdmission.admit dV OraclePortFrozen2.dV_frozen2
  split <;> rfl

theorem fibre_clean (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q) := by
  have hp : DecoderQueryAccounting.AdversaryQueries (pairProver s P) Q := by
    intro H; rw [pairProver_eval]; exact hq H
  have hb : OraclePortExperiment.Budget (dV s) :=
    OraclePortFrozen2.decision_budget s
  have checks := fibre_checks D s P Q hq
  have comp := OraclePortCompletionDraft.completion_of_checks D (dV s) (pairProver s P)
    (Q+1161) (fun H => by
      rw [OraclePortExperiment.original,OracleDecisionFeasibilityCore.original,
        RawCutProverCompiler.experiment_eval]
      have bound := VerifierCallBudget.firstReads_le_length emptyTable
        ((eval H (pairProver s P)).1 ++ (eval H (OraclePortExperiment.verifier D (dV s)
          (eval H (pairProver s P)).2.1 (eval H (pairProver s P)).2.2)).1)
      rw [List.length_append] at bound
      exact bound.trans (Nat.add_le_add (hp H)
        (OraclePortExperiment.verifier_budget D (dV s) hb H _ _))) checks
    (fun H ha => by
      rw [← admitted_dV s] at ha ⊢
      exact OraclePortAdmission.accepted_tag D (dV s) (pairProver s P) H ha)
  exact OraclePortConsumer.clean_of_checks D (dV s) (pairProver s P) Q hp hb comp checks

/-- All R16/R13/R15/R3/R14 model checks are discharged on the adaptive
stored experiment. The stored input is never fixed under the probability law. -/
theorem clean (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    CleanAcceptedModel D (projected D P) (bad Q) := by
  intro H run ha hn
  have same := (projected_eval D P H).trans (annotated_selected D dV P H)
  have model := fibre_clean D (eval H P).2.stored P Q hq H
  rw [← same] at model
  exact model ha hn

#print axioms projected_eval
#print axioms fibre_checks
#print axioms admitted_dV
#print axioms fibre_clean
#print axioms clean
end AspisR1.OraclePortFrozen2Consumer
end
