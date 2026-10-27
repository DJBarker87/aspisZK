import F3K_OpeningCalls
import F3K_SamplerOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryOne
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
    (eval H (F3J_SamplerRun.program pf 31 1 P)).1=
      observe (run (PreparedQueryEffects.queries effects
        (Query31ConcreteMaterializedSchedule.concreteBoundaries Query31ConcreteDriverTraceFacts.sourceDefaultState embed)
        D c.t4 31#u8 v.final_message)).1 ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 31 1 P)).2)=decodeState c.t5.state := by
  let pf := F3J_InputRows.proof p root w bound
  let P32 := F3K_SamplerOne.next H pf 31 P
  let P33 := F3K_SamplerOne.next H pf 32 P32
  have row31 := F3K_QueryFull.exact_row D embed c.t4 c.t5 v.final_message c.queries c.queryCall
    H backend (F3K_PayloadFits.fits v.final_message (rowBytes p 31) c.frame31 (bound 31))
    P (pf 31) ⟨rowBytes p 31,bound 31⟩
    (by rw [F3J_InputRows.erased,if_neg (by decide)]) state c.frame31
  have one := F3K_SamplerOne.one H pf 31 P
  constructor
  · exact (congrArg Prod.fst one).trans (congrArg Prod.fst row31)
  · rw [one]
    change UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (F3K_SamplerOne.next H pf 31 P))=_
    rw [F3K_SamplerOne.state]
    exact congrArg (fun r=>r.2.2) row31

#print axioms sampler
end AspisR1.F3K_QueryOne
end
