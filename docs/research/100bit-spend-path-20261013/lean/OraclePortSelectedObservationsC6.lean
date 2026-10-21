import OraclePortCandidateChecksC4
import OraclePortSelectedArithmeticC4

/-! The arithmetic checker consumes 22 local observations. The scalar record
has both whole words replaced by zero; no unqueried word survives projection.
The observation stores the first fold of the opened initial fibre, its opened
value, and the second fold of the opened final fibre. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSelectedObservationsC6
open LiteralAcceptanceTerminal
open OraclePortSelectedArithmeticC4
open AspisPool.AlgorithmicCircleDecoderV7
attribute [local irreducible] FirstFold.foldWord TwoFoldExtraction.batchedWord
  MatchingSupport.match0 MatchingSupport.AcceptedPairing QueryResidualBridge.values
  QueryResidualBridge.basis HchecksAccumulator.ClosedSum

structure Observation where
  scalars : MatchingSupport.Data E
  first : Fin 22 → E
  opened : Fin 22 → E
  second : Fin 22 → E

def observe (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144) : Observation :=
  ⟨withWords d (fun _ _ => 0) (fun _ => 0),
    fun j => FirstFold.foldWord d.alpha0 (TwoFoldExtraction.batchedWord d.W d.gamma) (q j),
    fun j => d.V (q j), QueryResidualBridge.values d q⟩

def Writer (o : Observation) : Prop := ∀ j, o.first j = o.opened j

def Backend (o : Observation) (q : Fin 22 → Fin 262144)
    (rho : AspisV8R15.ExactTowerBase.QM31Exact) : Prop :=
  MatchingSupport.AcceptedPairing o.scalars ∧
    (∑ l : Fin 64, o.scalars.f l * LiteralOpeningView.eK
      (∑ j : Fin 22, rho ^ j.val * QueryResidualBridge.basis q j l)) =
      ∑ j : Fin 22, (LiteralOpeningView.eK rho) ^ j.val * o.second j

theorem writer_iff (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144) :
    Writer (observe d q) ↔ ∀ j, MatchingSupport.match0 d (q j) := by
  unfold Writer observe MatchingSupport.match0
  rfl

theorem backend_iff (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144)
    (rho : AspisV8R15.ExactTowerBase.QM31Exact) :
    Backend (observe d q) q rho ↔ MatchingSupport.AcceptedPairing d ∧
      HchecksAccumulator.ClosedSum LiteralOpeningView.eK d q rho := by
  unfold Backend observe HchecksAccumulator.ClosedSum
  rw [← pairing d (fun _ _ => 0) (fun _ => 0)]
  rfl

/-- Only selected initial fibres, selected V values and selected final fibres
are needed. Scalar equality is supplied by the transcript, never word equality. -/
theorem observe_withWords (d : MatchingSupport.Data E)
    (W : Fin 29 → InitialWord E) (V : FinalWord E) (q : Fin 22 → Fin 262144)
    (initial : ∀ j lane, FirstFold.fibre (d.W lane) (q j) = FirstFold.fibre (W lane) (q j))
    (opened : ∀ j, d.V (q j) = V (q j))
    (folded : ∀ j slot, d.V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot) =
      V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot)) :
    observe d q = observe (withWords d W V) q := by
  have first : (fun j => FirstFold.foldWord d.alpha0
      (TwoFoldExtraction.batchedWord d.W d.gamma) (q j)) =
      (fun j => FirstFold.foldWord d.alpha0
      (TwoFoldExtraction.batchedWord W d.gamma) (q j)) := by
    funext j
    exact first_fold _ _ _ _ (batched_fibre _ _ _ _ (initial j))
  have second : QueryResidualBridge.values d q =
      QueryResidualBridge.values (withWords d W V) q :=
    funext (fun j => second_value d W V q j (folded j))
  change Observation.mk _ _ _ _ = Observation.mk _ _ _ _
  exact congrArg₂ (fun a b => Observation.mk
    (withWords d (fun _ _ => 0) (fun _ => 0)) a b
    (QueryResidualBridge.values d q)) first (funext opened) |>.trans
      (congrArg (fun v => Observation.mk
        (withWords d (fun _ _ => 0) (fun _ => 0))
        (fun j => FirstFold.foldWord d.alpha0 (TwoFoldExtraction.batchedWord W d.gamma) (q j))
        (fun j => V (q j)) v) second)

/-- D0 acceptance implies precisely these observation predicates, for any
successfully decoded query vector; reader equality is used only to identify
its scalar record. -/
theorem typed_accepted (rs : TranscriptRounds) (i : RecordedBinaryExperimentBin.SourceInputs)
    (q : Fin 22 → Fin 262144) (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (accepted : D0TypedChecks.verify rs i = true) :
    Writer (observe i.data q) ∧
      Backend (observe i.data q) q (SelectedChallengeMap.rhoOf i.rho) := by
  obtain ⟨matching,pairing,_,_,accumulator⟩ := D0TypedChecks.accepted_components rs i accepted
  exact ⟨(writer_iff _ _).2 (D0TypedChecks.accepted_writer rs i accepted q decoded),
    (backend_iff _ _ _).2 ⟨(LiteralPairingChecks.acceptedPairing_iff_checks rs i.data matching).2
      pairing,accumulator q decoded⟩⟩

/-- Acceptance of the specified stored decision supplies observation checks.
This theorem does not rename that draft arithmetic candidate a frozen verifier. -/
theorem stored_accepted (stored : AspisV8R19.DuplexFrames.Bytes)
    (tr : RawCutTranscriptRun.ErasedPrefix) (m : RawCutTranscriptRun.ErasedMessage)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (accepted : (AspisV8R19.MemoizedProgramLaw.eval H
      (OraclePortStoredDecisionDraftC4.decision stored tr m)).2 = true) :
    ∃ p q i, OraclePortStoredParserC4.parseReached stored tr = some p ∧
      OraclePortSelectedDraft.queries tr = some q ∧
      OraclePortStoredDecisionDraftC4.input p q tr = some i ∧
      Writer (observe i.data q) ∧
      Backend (observe i.data q) q (SelectedChallengeMap.rhoOf i.rho) := by
  obtain ⟨_,p,q,i,parsed,query,_,_,input,checked⟩ :=
    OraclePortStoredDecisionDraftC4.accepted stored tr m H accepted
  have fields := (OraclePortStoredDecisionDraftC4.input_fields p q tr i input).1
  have decoded : LiteralQueryRead.decode i.queryBytes = some q := by
    simpa [OraclePortSelectedDraft.queries,fields.2.1] using query
  exact ⟨p,q,i,parsed,query,input,typed_accepted _ i q decoded checked⟩

#print axioms writer_iff
#print axioms backend_iff
#print axioms observe_withWords
#print axioms typed_accepted
#print axioms stored_accepted
end AspisR1.OraclePortSelectedObservationsC6
end
