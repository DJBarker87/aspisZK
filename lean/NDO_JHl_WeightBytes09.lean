import NDO_JHl_WeightCell
import NDO_JHl_Weight35_38
import NDO_JHl_Weight39_42
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes09
open Aeneas Aeneas.Std

theorem cell36 : JHl_WeightCell.Law ⟨36,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight35_38.source36
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 36 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight36.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1288).take 16
  rw [JFq_Weight36.selected]
  exact bytes.trans (by rfl)
#print axioms cell36

theorem cell37 : JHl_WeightCell.Law ⟨37,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight35_38.source37
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 37 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight37.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1304).take 16
  rw [JFq_Weight37.selected]
  exact bytes.trans (by rfl)
#print axioms cell37

theorem cell38 : JHl_WeightCell.Law ⟨38,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight35_38.source38
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 38 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight38.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1320).take 16
  rw [JFq_Weight38.selected]
  exact bytes.trans (by rfl)
#print axioms cell38

theorem cell39 : JHl_WeightCell.Law ⟨39,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight39_42.source39
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 39 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight39.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1336).take 16
  rw [JFq_Weight39.selected]
  exact bytes.trans (by rfl)
#print axioms cell39
end AspisR1.JHl_WeightBytes09
end
