import NDO_JHl_WeightCell
import NDO_JHl_Weight51_54
import NDO_JHl_Weight55_58
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes13
open Aeneas Aeneas.Std

theorem cell52 : JHl_WeightCell.Law ⟨52,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight51_54.source52
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 52 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight52.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1544).take 16
  rw [JFq_Weight52.selected]
  exact bytes.trans (by rfl)
#print axioms cell52

theorem cell53 : JHl_WeightCell.Law ⟨53,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight51_54.source53
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 53 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight53.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1560).take 16
  rw [JFq_Weight53.selected]
  exact bytes.trans (by rfl)
#print axioms cell53

theorem cell54 : JHl_WeightCell.Law ⟨54,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight51_54.source54
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 54 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight54.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1576).take 16
  rw [JFq_Weight54.selected]
  exact bytes.trans (by rfl)
#print axioms cell54

theorem cell55 : JHl_WeightCell.Law ⟨55,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight55_58.source55
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 55 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight55.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1592).take 16
  rw [JFq_Weight55.selected]
  exact bytes.trans (by rfl)
#print axioms cell55
end AspisR1.JHl_WeightBytes13
end
