import NDO_JHl_CurrentWeights
import JHk_KUnique
import NDO_JHk_PreparedScalarBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightCell
open Aeneas Aeneas.Std

def encoded (q : AspisR1CurrentCaller.aspis_core.field.QM31) : List U8 :=
  (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k q))).map
    CheckpointBytes5Writer.u8

def Law (j : Fin 64) : Prop :=
  ∀ q : AspisR1CurrentCaller.aspis_core.field.QM31,
    Port3_FlushInstall.Canonical (Tx1Q_Carriers.k q) →
    CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 j.val →
    encoded q=(JFx_NativeBytes.checkpoint.val.drop (712+16*j.val)).take 16

theorem equal (q : AspisR1CurrentCaller.aspis_core.field.QM31)
    (target : AspisR1Stage2.aspis_core.field.QM31)
    (hc : Port3_FlushInstall.Canonical (Tx1Q_Carriers.k q))
    (ht : Port3_FlushInstall.Canonical target)
    (same : CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=CheckpointBytes5Output.ofK target) :
    encoded q=(WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK target)).map CheckpointBytes5Writer.u8 := by
  unfold encoded
  rw [JHk_KUnique.source _ _ hc ht same]
#print axioms equal
end AspisR1.JHl_WeightCell
end
