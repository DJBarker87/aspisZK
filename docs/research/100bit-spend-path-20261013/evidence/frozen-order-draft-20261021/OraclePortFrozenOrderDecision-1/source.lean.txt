import OraclePortFrozenOrderSlot
import OraclePortShortCircuitDecision

/-! New model only. The old global recursive-tree Padding guard is replaced
by each frozen slot's post-leaf node_count/padding check, in source order.
The six outer slots short circuit. No production/source refinement is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozenOrder
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredExperimentC4
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
attribute [local instance] Classical.propDecidable

def slotPrograms (p : Parsed) (q : Fin 22 → Fin 262144) (ss : List (Nat × Nat)) :=
  ss.map fun s => verifySlot_frozen p q s.1 s.2

def dV_frozen : Decision := fun stored tr _ =>
  if OraclePortAdmission.Guard tr then
    match OraclePortStoredParserC4.parseReached stored tr, queries tr with
    | some p, some q =>
        bind (OraclePortShortCircuit.short (slotPrograms p q slots)) fun ok =>
          .done (ok && OraclePortStoredDecisionDraftC4.arithmetic p q tr)
    | _, _ => .done false
  else .done false

theorem admitted (stored : Bytes) :
    OraclePortAdmission.admit (dV_frozen stored) = dV_frozen stored := by
  funext tr m
  unfold OraclePortAdmission.admit dV_frozen
  split <;> rfl

theorem accepted (stored : Bytes) (tr : ErasedPrefix) (m : ErasedMessage)
    (H : Bytes → State) (ha : (eval H (dV_frozen stored tr m)).2 = true) :
    OraclePortAdmission.Guard tr ∧ ∃ p q,
      OraclePortStoredParserC4.parseReached stored tr = some p ∧ queries tr = some q ∧
      (eval H (OraclePortShortCircuit.short (slotPrograms p q slots))).2 = true ∧
      OraclePortStoredDecisionDraftC4.arithmetic p q tr = true := by
  unfold dV_frozen at ha
  split at ha
  · rename_i guard
    refine ⟨guard, ?_⟩
    split at ha
    · rename_i p q hp hq
      exact ⟨p,q,hp,hq,by simpa only [eval_bind,eval,Bool.and_eq_true] using ha⟩
    · simp only [eval,Bool.false_eq_true] at ha
  · simp only [eval,Bool.false_eq_true] at ha

#print axioms admitted
#print axioms accepted
end AspisR1.OraclePortFrozenOrder
end
