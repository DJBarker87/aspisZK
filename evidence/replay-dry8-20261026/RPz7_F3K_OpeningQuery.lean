import RPz7_F3K_OpeningFirst4
import RPz7_F3K_SamplerIndex
import RPz7_F3K_SourceQueryDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_OpeningQuery
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft

theorem queries {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=27)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state) :
    let pf := F3J_InputRows.proof p root w bound
    OraclePortSelectedDraft.queries (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 27 6 P)).2)=
      LiteralQueryRead.decode (c.queries.val.map (fun x=>x.val)) := by
  let pf := F3J_InputRows.proof p root w bound
  let P31 := (eval H (F3J_SamplerRun.program pf 27 4 P)).2
  have first := F3K_OpeningFirst4.sampler c H backend root w bound P state
  have len31 : P31.rounds.length=31 := by
    have len := F3J_SamplerRun.length H pf 27 4 P
    rw [length] at len
    exact len
  have row31 := F3K_QueryFull.exact_row D embed c.t4 c.t5 v.final_message c.queries c.queryCall
    H backend (F3K_PayloadFits.fits v.final_message (rowBytes p 31) c.frame31 (bound 31))
    P31 (pf 31) ⟨rowBytes p 31,bound 31⟩
    (by rw [F3J_InputRows.erased,if_neg (by decide)]) first.2 c.frame31
  have entry := F3K_SamplerIndex.first_entry H pf 31 1 P31
  rw [len31,congrArg Prod.snd row31] at entry
  change OraclePortSelectedDraft.queries
    (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 27 (4+2) P)).2)=_
  rw [F3J_SamplerCompose.value H pf 27 4 2 P]
  unfold OraclePortSelectedDraft.queries LiteralTranscript.erasePrefix
  simp only [List.getElem?_map]
  erw [entry]
  rfl

theorem decoded {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=27)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state) :
    ∃ q, OraclePortSelectedDraft.queries (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 27 6 P)).2)=some q ∧
      ∀ j : Fin 22,(c.queries.val[j.val]'(by have len : c.queries.val.length=22:=c.queries.property;omega)).val=(q j).val := by
  obtain ⟨q,decode,coordinates⟩ := F3K_SourceQueryDecode.source D embed c.t4 c.t5 v.final_message c.queries c.queryCall
  exact ⟨q,(queries c H backend root w bound P length state).trans decode,coordinates⟩

#print axioms queries
#print axioms decoded
end AspisR1.F3K_OpeningQuery
end
