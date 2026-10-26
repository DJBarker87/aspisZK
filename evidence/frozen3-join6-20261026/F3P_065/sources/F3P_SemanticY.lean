import F3P_DecodeCircleIndex
import F3P_SemanticDecode
import F3P_InputY
import F3J_RecordPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_SemanticY
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation OraclePortCompactDraft

theorem extra_before {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (pre : r1_wire.Prefix) (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children B D pub bytes hash=ok (.Ok sem))
    (p : Parsed) (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : OraclePortStoredDecisionDraftC4.input p q tr=some i) :
    (∀ (l : Usize) (hl : l.val<29) scalar,
      Array.index_usize (retainedSem sem).extra l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=i.data.Y 3 ⟨l.val,hl⟩) ∧
    (∀ (l : Usize) (hl : l.val<29) scalar,
      Array.index_usize (retainedSem sem).before_z1 l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=i.data.Y 4 ⟨l.val,hl⟩) := by
  obtain ⟨r25,r26,read25,extra,read26,before,claims⟩ := F3P_SemanticDecode.cells
    AspisS1ExtractedRoundChildren.children B D pub bytes hash sem pre parsed success
  obtain ⟨v25,v26,v27,model25,model26,model27,Y⟩ := F3P_InputY.rows p q tr aligned i found
  have physical25 := F3J_RecordPayload.row_bytes pre r25 25#u8 p records (by decide) read25
  have physical26 := F3J_RecordPayload.row_bytes pre r26 26#u8 p records (by decide) read26
  change rowBytes p 25=MultiproofConeCanonical.bytesOf r25.framed.val at physical25
  change rowBytes p 26=MultiproofConeCanonical.bytesOf r26.framed.val at physical26
  rw [physical25] at model25
  rw [physical26] at model26
  constructor
  · intro l hl scalar read
    rw [Y,SelectedOpeningClaims.Y_extra]
    exact F3P_DecodeCircleIndex.cell r25 87#usize _ extra 0 v25 model25 l hl (by change 87+l.val<116;omega) scalar read
  · intro l hl scalar read
    rw [Y,SelectedOpeningClaims.Y_beforeZ1]
    exact F3P_DecodeCircleIndex.cell r26 0#usize _ before 1 v26 model26 l hl (by change 0+l.val<29;omega) scalar read

#print axioms extra_before
end AspisR1.F3P_SemanticY
end
