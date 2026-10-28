import NDO_JHl_WeightCell
import NDO_JHl_Weight43_46
import NDO_JHl_Weight47_50
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes11
open Aeneas Aeneas.Std

theorem cell44 : JHl_WeightCell.Law ⟨44,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight43_46.source44
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 44 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight44.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1416).take 16
  rw [JFq_Weight44.selected]
  exact bytes.trans (by rfl)
#print axioms cell44

theorem cell45 : JHl_WeightCell.Law ⟨45,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight43_46.source45
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 45 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight45.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1432).take 16
  rw [JFq_Weight45.selected]
  exact bytes.trans (by rfl)
#print axioms cell45

theorem cell46 : JHl_WeightCell.Law ⟨46,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight43_46.source46
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 46 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight46.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1448).take 16
  rw [JFq_Weight46.selected]
  exact bytes.trans (by rfl)
#print axioms cell46

theorem cell47 : JHl_WeightCell.Law ⟨47,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight47_50.source47
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 47 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight47.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1464).take 16
  rw [JFq_Weight47.selected]
  exact bytes.trans (by rfl)
#print axioms cell47
end AspisR1.JHl_WeightBytes11
end
