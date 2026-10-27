import RPz7_F3P_ClaimsCells
import RPz7_F3P_SemanticClaims
import RPz7_F3P_SemanticDecode
import RPz7_F3P_InputY
import RPz7_F3J_RecordPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_SemanticClaimsY
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation OraclePortCompactDraft

theorem claims {H : Type} (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (pre : r1_wire.Prefix) (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B) D pub bytes hash=ok (.Ok sem))
    (p : Parsed) (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : OraclePortStoredDecisionDraftC4.input p q tr=some i) :
    ∀ (point l : Usize) (hp : point.val<3) (hl : l.val<29) row scalar,
      Array.index_usize (retainedSem sem).claims point=ok row → Array.index_usize row l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=i.data.Y ⟨point.val,by omega⟩ ⟨l.val,hl⟩ := by
  obtain ⟨r,a,b,c,read25,d0,d1,d2,claimRows⟩ := F3P_SemanticClaims.rows B std D pub bytes hash sem pre parsed success
  obtain ⟨v25,v26,v27,model25,model26,model27,Y⟩ := F3P_InputY.rows p q tr aligned i found
  have physical := F3J_RecordPayload.row_bytes pre r 25#u8 p records (by decide) read25
  change rowBytes p 25=MultiproofConeCanonical.bytesOf r.framed.val at physical
  rw [physical] at model25
  intro point l hp hl row scalar readRow read
  rw [claimRows] at readRow
  rw [Y,SelectedOpeningClaims.Y_point v25 v26 v27 ⟨point.val,hp⟩ ⟨l.val,hl⟩]
  exact F3P_ClaimsCells.cells r a b c d0 d1 d2 v25 model25 point l hp hl row scalar readRow read

#print axioms claims
end AspisR1.F3P_SemanticClaimsY
end
