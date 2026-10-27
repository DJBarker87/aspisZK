import F3L_OpeningDataFields
import F3L_OpeningInputLate
import F3L_SourceAlphaIndex
import F3L_RhoCanonical
import F3K_OpeningQuery
import Port5Q1_QueryPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_PreparePort
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] closedHashBoundaries F3J_InputRows.proof F3J_SamplerRun.program

theorem port {Hash : Type} {D : aspis_core.Digest32 Hash}
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
    Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared (currentPrepared out))
      i.data q (SelectedChallengeMap.rhoOf i.rho) := by
  have sourceFields := F3K_PreparedSourceFields.fields s
  have dataFields := F3L_OpeningDataFields.fields s.c H backend root w bound P length state q i.data
    (input_fields p q _ i found).2
  have late := F3L_OpeningInputLate.fields s.c H backend root w bound P length state q i found
  have queryEq := F3K_OpeningQuery.queries s.c H backend root w bound P length state
  obtain ⟨q0,decoded,coordinates⟩ := F3K_SourceQueryDecode.source D embed s.c.t4 s.c.t5 v.final_message
    s.c.queries s.c.queryCall
  have same : q0=q := Option.some.inj (decoded.symm.trans (queryEq.symm.trans query))
  subst q0
  refine ⟨?_,?_,?_,?_⟩
  · intro j below
    change (Port5Q1_GeometryBinding.queryAt out.queries j).val=_
    rw [sourceFields.2.2.2.2.2.1]
    have boundj : j<s.c.queries.val.length := by have h : s.c.queries.val.length=22:=s.c.queries.property;omega
    simp only [Port5Q1_GeometryBinding.queryAt,List.getElem?_eq_getElem boundj,Option.getD_some]
    exact coordinates ⟨j,below⟩
  · change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k (currentQ out.rho))=_
    rw [F3L_SourceNumeric.qm,sourceFields.2.2.2.2.1,late.1]
    rfl
  · change Port3_FlushInstall.Canonical (Tx1Q_Carriers.k (currentQ out.rho))
    rw [sourceFields.2.2.2.2.1]
    exact F3L_RhoCanonical.scalar D closedHashBoundaries.sampling s.c.t5 s.c.t6
      PreparedScratchReachability.emptyPayload s.c.rho s.c.rhoCall
  · intro alpha read
    rw [F3L_SourceAlphaIndex.alpha1 s alpha read,F3L_SourceNumeric.wide]
    exact dataFields.2.2.2.symm

#print axioms port
end AspisR1.F3L_PreparePort
end
