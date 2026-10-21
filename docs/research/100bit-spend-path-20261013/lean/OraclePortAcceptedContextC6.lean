import OraclePortSelectedObservationsC6
import OraclePortCheckpointOracleC5

/-! Reconstruct the checkpoint model context from a reached accepted parser
and its typed reader. No free Context parameter is accepted. The remaining
Rust Prepared::new / caller refinement is not a consequence of this model law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortAcceptedContextC6
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralAcceptanceTerminal OraclePortCompactDraft OraclePortSelectedDraft
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local irreducible] OraclePortCheckpointStateC3.write QueryAccumulator.run22
  QueryResidualBridge.values QueryResidualBridge.basis JointFunctionalBinding.claimedValue

/-- Source-order z0.x,z0.y,z1.x,z1.y, in the checkpoint subfield. -/
def coordinates (v : LiteralOpeningView.View) : Fin 4 → K := fun j =>
  if j.val = 0 then SelectedChallengeMap.rhoOf (v.circlePoints 0).1.1
  else if j.val = 1 then SelectedChallengeMap.rhoOf (v.circlePoints 0).1.2
  else if j.val = 2 then SelectedChallengeMap.rhoOf (v.circlePoints 1).1.1
  else SelectedChallengeMap.rhoOf (v.circlePoints 1).1.2

/-- Both semantic roots are retained; the third (folded) root remains in the
retained proof bytes. The prepared claim is the batched opening claim, not
the semantic mask-sum claim at row fourteen. -/
def context (p : Parsed) (i : SourceInputs) (v : LiteralOpeningView.View) : Context :=
  ⟨i.state32,
    (fun j => OraclePortBatchDraft.committedRoot p j.val),
    (fun j => SelectedChallengeMap.rhoOf ((v.semantic.map Prod.snd).getD (15+j.val) 0)),
    coordinates v,
    JointFunctionalBinding.claimedValue i.data.Y i.data.c0 i.data.gamma i.data.kappa⟩

def ContextFields (p : Parsed) (i : SourceInputs) (v : LiteralOpeningView.View) (c : Context) : Prop :=
  c.state = i.state32 ∧
  (∀ j, c.roots j = OraclePortBatchDraft.committedRoot p j.val) ∧
  (∀ j, c.semanticAlpha j = SelectedChallengeMap.rhoOf
    ((v.semantic.map Prod.snd).getD (15+j.val) 0)) ∧
  c.coordinates = coordinates v ∧
  c.claim = JointFunctionalBinding.claimedValue i.data.Y i.data.c0 i.data.gamma i.data.kappa

theorem context_fields (p : Parsed) (i : SourceInputs) (v : LiteralOpeningView.View) :
    ContextFields p i v (context p i v) := ⟨rfl,fun _ => rfl,fun _ => rfl,rfl,rfl⟩

theorem saved_prepared (H : Bytes → State) (stored pub : Bytes)
    (p : Parsed) (i : SourceInputs) (v : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144) :
    OraclePortCheckpointPreparedC5.decode
      (save H stored pub (context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q).checkpoint =
      some (prepared (context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q) :=
  OraclePortCheckpointPreparedC5.decode_encode H stored pub _ _

/-- The context, source inputs, reader, and saved state now share the same
accepted parser witness. The six hashes remain inside the oracle program. -/
theorem accepted_context (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) (H : Bytes → State)
    (accepted : (eval H (OraclePortStoredDecisionDraftC4.decision stored tr m)).2 = true) :
    ∃ p q i v,
      OraclePortStoredParserC4.parseReached stored tr = some p ∧
      queries tr = some q ∧ D0InstanceAdmission.Fields tr i ∧
      LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows p q tr) = some i.data ∧
      LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr) = some v ∧
      ContextFields p i v (context p i v) ∧
      OraclePortCheckpointPreparedC5.decode
        (save H stored tr.statement.pubBytes (context p i v) i.data
          (SelectedChallengeMap.rhoOf i.rho) q).checkpoint =
        some (prepared (context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q) ∧
      (eval H (OraclePortCheckpointOracleC5.writeResume stored tr.statement.pubBytes
        (context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q)).2 =
        some (QueryAccumulator.run22 LiteralOpeningView.eK (SelectedChallengeMap.rhoOf i.rho)
          (QueryResidualBridge.values i.data q) (QueryResidualBridge.basis q)) := by
  obtain ⟨_,p,q,i,parsed,query,_,_,input,checked⟩ :=
    OraclePortStoredDecisionDraftC4.accepted stored tr m H accepted
  have fields := (OraclePortStoredDecisionDraftC4.input_fields p q tr i input).1
  have matching := D0TypedChecks.accepted_matching _ i checked
  obtain ⟨v,_,_,opening,_,_⟩ := HchecksReaderComposition.matching_read_parsers _ i.data matching
  exact ⟨p,q,i,v,parsed,query,fields,matching,opening,context_fields p i v,
    saved_prepared H stored tr.statement.pubBytes p i v q,
    OraclePortCheckpointOracleC5.writeResume_value H stored tr.statement.pubBytes
      (context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q⟩

#print axioms context_fields
#print axioms saved_prepared
#print axioms accepted_context
end AspisR1.OraclePortAcceptedContextC6
end
