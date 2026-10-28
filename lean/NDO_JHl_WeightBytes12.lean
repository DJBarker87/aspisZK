import NDO_JHl_WeightCell
import NDO_JHl_Weight47_50
import NDO_JHl_Weight51_54
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes12
open Aeneas Aeneas.Std

theorem cell48 : JHl_WeightCell.Law ⟨48,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight47_50.source48
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 48 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight48.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1480).take 16
  rw [JFq_Weight48.selected]
  exact bytes.trans (by rfl)
#print axioms cell48

theorem cell49 : JHl_WeightCell.Law ⟨49,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight47_50.source49
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 49 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight49.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1496).take 16
  rw [JFq_Weight49.selected]
  exact bytes.trans (by rfl)
#print axioms cell49

theorem cell50 : JHl_WeightCell.Law ⟨50,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight47_50.source50
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 50 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight50.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1512).take 16
  rw [JFq_Weight50.selected]
  exact bytes.trans (by rfl)
#print axioms cell50

theorem cell51 : JHl_WeightCell.Law ⟨51,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight51_54.source51
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 51 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight51.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1528).take 16
  rw [JFq_Weight51.selected]
  exact bytes.trans (by rfl)
#print axioms cell51
end AspisR1.JHl_WeightBytes12
end
