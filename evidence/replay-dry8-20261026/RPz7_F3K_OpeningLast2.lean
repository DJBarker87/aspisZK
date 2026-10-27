import RPz7_F3K_QueryOne
import RPz7_F3K_RhoOne
import RPz7_F3K_SamplerOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_OpeningLast2
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft

theorem sampler {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t4.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (F3J_SamplerRun.program pf 31 2 P)).1=
      observe (run (PreparedQueryEffects.queries effects
        (Query31ConcreteMaterializedSchedule.concreteBoundaries Query31ConcreteDriverTraceFacts.sourceDefaultState embed)
        D c.t4 31#u8 v.final_message)).1 ++
      observe (run (PreparedScalarEffects.scalar_k effects B D c.t5 32#u8 PreparedScratchReachability.emptyPayload)).1 ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 31 2 P)).2)=decodeState c.t6.state := by
  let pf := F3J_InputRows.proof p root w bound
  have first := F3K_QueryOne.sampler c H backend root w bound P state
  let P32 := (eval H (F3J_SamplerRun.program pf 31 1 P)).2
  have second := F3K_RhoOne.rho D B c.t5 c.t6 PreparedScratchReachability.emptyPayload c.rho c.rhoCall
    H backend p root w bound c.frame32
    (F3K_PayloadFits.fits PreparedScratchReachability.emptyPayload (rowBytes p 32) c.frame32 (bound 32)) P32 first.2
  constructor
  · exact (F3J_SamplerCompose.logs H pf 31 1 1 P).trans (congrArg₂ List.append first.1 second.1)
  · exact (congrArg (fun Q=>UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix Q)) (F3J_SamplerCompose.value H pf 31 1 1 P)).trans second.2

#print axioms sampler
end AspisR1.F3K_OpeningLast2
end
