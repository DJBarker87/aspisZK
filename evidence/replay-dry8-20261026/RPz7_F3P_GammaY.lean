import RPz7_F3P_GammaField
import RPz7_F3P_InputY
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_GammaY
open Aeneas Aeneas.Std Result OraclePortCompactDraft

theorem cells (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : OraclePortStoredDecisionDraftC4.input p q tr=some i) (y1 : Slice U8)
    (frame : rowBytes p 27=LengthFrameCodec.frame (MultiproofConeCanonical.bytesOf y1.val)) :
    ∀ (l : Usize) (hl : l.val<29) parsed,
      AspisR1CurrentPreparedClaim.ClaimParser.field y1 l=ok parsed →
      AspisR1CurrentPreparedClaim.Concrete.Canonical parsed →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode (AspisR1ClaimPreparedBridge.fromClaimQ parsed.c0))=
        i.data.Y 5 ⟨l.val,hl⟩ := by
  obtain ⟨v25,v26,v27,model25,model26,model27,Y⟩ := F3P_InputY.rows p q tr aligned i found
  rw [frame] at model27
  intro l hl parsed source canonical
  rw [Y]
  exact F3P_GammaField.cell y1 v27 model27 l hl parsed source

#print axioms cells
end AspisR1.F3P_GammaY
end
