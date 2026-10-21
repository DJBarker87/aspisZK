import S8JoinModelRepresentation
import OraclePortFrozenOrderAccepted

/-! Total replacement of the frozen arithmetic's ClosedSum test by the
complete logical finish reference. Pure arithmetic creates no oracle reads.
This does not identify the canonical logical raw vector with Rust storage. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinFrozenArithmetic
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralAcceptanceTerminal RecordedBinaryExperimentBin
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
attribute [local instance] Classical.propDecidable

def verify (rs : TranscriptRounds) (i : SourceInputs) : Bool :=
  match LiteralMatchingData.read rs with
  | none => false
  | some data => decide (
      data = i.data ∧ LiteralPairingChecks.checks rs ∧
      R16DecisionQueryModel.verify data i.queryBytes = true ∧
      R3SemanticRemainingJoins.EquationEndpoint i.decoded rs data ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode i.queryBytes = some q →
        S8JoinModelRepresentation.modelCheck data q (SelectedChallengeMap.rhoOf i.rho) = true)

theorem verify_eq (rs : TranscriptRounds) (i : SourceInputs) :
    verify rs i = D0TypedChecks.verify rs i := by
  unfold verify D0TypedChecks.verify
  cases LiteralMatchingData.read rs with
  | none => rfl
  | some data =>
    apply Bool.eq_iff_iff.mpr
    simp only [S8JoinModelRepresentation.model_check_eq,decide_eq_true_eq]

def arithmetic (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) : Bool :=
  match input p q tr with
  | none => false
  | some i => verify (typedRows p q tr) i

/-- Equality includes rejected input and false final arithmetic. -/
theorem arithmetic_eq (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) :
    arithmetic p q tr = OraclePortStoredDecisionDraftC4.arithmetic p q tr := by
  unfold arithmetic OraclePortStoredDecisionDraftC4.arithmetic
  cases input p q tr <;> simp only [verify_eq]

/-- Keep the frozen multiproof schedule and all rejection paths; substitute
only the complete logical S8 arithmetic reference. -/
def decision : OraclePortStoredExperimentC4.Decision := fun stored tr _ =>
  if OraclePortAdmission.Guard tr then
    match OraclePortStoredParserC4.parseReached stored tr,OraclePortSelectedDraft.queries tr with
    | some p,some q => bind (OraclePortShortCircuit.short
        (OraclePortFrozenOrder.slotPrograms p q OraclePortBatchDraft.slots)) fun ok =>
        .done (ok && arithmetic p q tr)
    | _,_ => .done false
  else .done false

/-- Total Program equality, hence the exact ordered log as well as result. -/
theorem decision_eq : decision=OraclePortFrozenOrder.dV_frozen := by
  funext stored tr m
  simp only [decision,OraclePortFrozenOrder.dV_frozen,arithmetic_eq]

/-- The finish reference is accepted at the exact reached model input/query.
No collision-free assumption is needed for this deterministic arithmetic fact. -/
theorem accepted_reference (stored : Bytes) (tr : ErasedPrefix) (m : ErasedMessage)
    (H : Bytes → State)
    (accepted : (eval H (OraclePortFrozenOrder.dV_frozen stored tr m)).2=true) :
    ∃ p q i, OraclePortStoredParserC4.parseReached stored tr=some p ∧
      OraclePortSelectedDraft.queries tr=some q ∧ input p q tr=some i ∧
      S8JoinModelRepresentation.modelCheck i.data q (SelectedChallengeMap.rhoOf i.rho)=true := by
  obtain ⟨_,p,q,i,hp,hq,_,hi,hv⟩ :=
    OraclePortFrozenOrder.accepted_details stored tr m H accepted
  have fields := (input_fields p q tr i hi).1
  have decoded : LiteralQueryRead.decode i.queryBytes=some q := by
    simpa [OraclePortSelectedDraft.queries,fields.2.1] using hq
  have closed := (D0TypedChecks.accepted_backend _ i hv).2 q decoded
  exact ⟨p,q,i,hp,hq,hi,by
    rw [S8JoinModelRepresentation.model_check_eq]
    exact decide_eq_true closed⟩

/-- Certificate conditions at the construction-owned reached model state.
This supplies the exact old natural-coordinate P6 interface, without treating
that logical vector as an authenticated Rust/checkpoint vector. -/
theorem accepted_model_caller (stored : Bytes) (tr : ErasedPrefix) (m : ErasedMessage)
    (H : Bytes → State)
    (accepted : (eval H (OraclePortFrozenOrder.dV_frozen stored tr m)).2=true) :
    ∃ p q i, OraclePortStoredParserC4.parseReached stored tr=some p ∧
      OraclePortSelectedDraft.queries tr=some q ∧ input p q tr=some i ∧
      S8Kani2CallerJoin.CallerInvariant
        (S8JoinModelRepresentation.raw (S8JoinAccumulatorStage.weight q (SelectedChallengeMap.rhoOf i.rho)))
        S8JoinModelRepresentation.old
        (fun j k => if h:j<64 then
          (S8JoinModelRepresentation.limb
            (S8JoinAccumulatorStage.weight q (SelectedChallengeMap.rhoOf i.rho) ⟨j,h⟩) k).val else 0) := by
  obtain ⟨p,q,i,hp,hq,hi,_⟩ := accepted_reference stored tr m H accepted
  exact ⟨p,q,i,hp,hq,hi,S8JoinModelRepresentation.model_caller _⟩

#print axioms verify_eq
#print axioms arithmetic_eq
#print axioms decision_eq
#print axioms accepted_reference
#print axioms accepted_model_caller
end AspisR1.S8JoinFrozenArithmetic
end
