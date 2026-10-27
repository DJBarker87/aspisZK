import RPz7_F3L_PreparePort
import RPz7_F3L_SourceAlphaValues
import RPz7_F3L_PreparedQueryPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_PreparedModelSix
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] closedHashBoundaries F3J_InputRows.proof F3J_SamplerRun.program

def Fields (out : verifier.Prepared) (i : RecordedBinaryExperimentBin.SourceInputs)
    (q : Fin 22 → Fin 262144) : Prop :=
  let p := F3L_SourcePrepared.numeric out
  p.gamma=i.data.gamma ∧ p.kappa=i.data.kappa ∧
  p.alpha=(fun j=>if j.val=0 then i.data.alpha0 else i.data.alpha1) ∧
  p.rho=SelectedChallengeMap.rhoOf i.rho ∧ p.queries=q ∧ p.state=i.state32

theorem fields {Hash : Type} {D : aspis_core.Digest32 Hash}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {sem : r1_semantic.Verified Hash} {v : verifier.View} {hash : Hash}
    {p : Parsed} {out : verifier.Prepared} {scratch : Array aspis_core.field.WideExact 29#usize}
    (s : F3K_OpeningSpine.Spine D closedHashBoundaries embed sem v hash p out scratch)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=27)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState s.c.t0.state)
    (q : Fin 22 → Fin 262144) (i : RecordedBinaryExperimentBin.SourceInputs)
    (query : OraclePortSelectedDraft.queries (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 27 6 P)).2)=some q)
    (found : input p q (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 27 6 P)).2)=some i) :
    Fields out i q := by
  have source := F3K_PreparedSourceFields.fields s
  have data := F3L_OpeningDataFields.fields s.c H backend root w bound P length state q i.data
    (input_fields p q _ i found).2
  have late := F3L_OpeningInputLate.fields s.c H backend root w bound P length state q i found
  have port := F3L_PreparePort.port s H backend root w bound P length state q i query found
  refine ⟨?_,?_,?_,?_,F3L_PreparedQueryPort.queries _ _ _ _ port,?_⟩
  · change AspisR1CurrentPreparedClaim.Concrete.decode (AspisR1ClaimPreparedBridge.toClaimE out.gamma)=_
    rw [source.2.1]
    exact data.1.symm
  · change AspisR1CurrentPreparedClaim.Concrete.decode (AspisR1ClaimPreparedBridge.toClaimE out.kappa)=_
    rw [source.2.2.1]
    exact data.2.1.symm
  · rw [F3L_SourceAlphaValues.alpha s]
    funext j
    by_cases zero : j.val=0
    · rw [if_pos zero,if_pos zero,data.2.2.1]
    · rw [if_neg zero,if_neg zero,data.2.2.2]
  · change F3L_RhoMeaning.decode out.rho=_
    rw [source.2.2.2.2.1,late.1]
    rfl
  · change decodeState out.state=i.state32
    rw [source.2.2.2.2.2.2.1]
    exact late.2.symm

#print axioms fields
end AspisR1.F3L_PreparedModelSix
end
