import F3L_OpeningLateEntries
import F3L_LateFields
import F3L_SamplerStatement
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OpeningFields
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem fields {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=27)
    (parsedPublic : ∃ decoded,SemanticPublicWire.parsePublic P.statement.pubBytes=some decoded)
    (data : MatchingSupport.Data LiteralTranscript.E)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state) :
    ∃ i,D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 27 6 P)).2) i := by
  let pf := F3J_InputRows.proof p root w bound
  let Q := (eval H (F3J_SamplerRun.program pf 27 6 P)).2
  obtain ⟨decoded,decodedPublic⟩ := parsedPublic
  have entries := F3L_OpeningLateEntries.entries c H backend root w bound P length state
  apply F3L_LateFields.exists_fields _ decoded (pf 31) (pf 32)
    (c.queries.val.map (fun x=>x.val)) (LiteralOpeningView.eK (F3L_RhoMeaning.decode c.rho))
    (decodeState c.t5.state) (decodeState c.t6.state) data
  · change SemanticPublicWire.parsePublic Q.statement.pubBytes=some decoded
    rw [F3L_SamplerStatement.statement]
    exact decodedPublic
  · simp only [LiteralTranscript.erasePrefix,List.getElem?_map,entries.1,Option.map_some]
  · simp only [LiteralTranscript.erasePrefix,List.getElem?_map,entries.2,Option.map_some]
  · exact F3J_InputRows.valid p root w bound 31 (by decide)
  · exact F3J_InputRows.valid p root w bound 32 (by decide)

#print axioms fields
end AspisR1.F3L_OpeningFields
end
