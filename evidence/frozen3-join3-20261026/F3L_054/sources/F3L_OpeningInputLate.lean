import F3L_LateFieldEquality
import F3L_OpeningLateEntries
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OpeningInputLate
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

theorem fields {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=27)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state)
    (q : Fin 22 → Fin 262144) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : input p q (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 27 6 P)).2)=some i) :
    i.rho=LiteralOpeningView.eK (F3L_RhoMeaning.decode c.rho) ∧ i.state32=decodeState c.t6.state := by
  have entries := F3L_OpeningLateEntries.entries c H backend root w bound P length state
  exact F3L_LateFieldEquality.rho_state _ i (input_fields p q _ i found).1 _ _ _ entries.2

#print axioms fields
end AspisR1.F3L_OpeningInputLate
end
