import NDO_JHl_WeightCell
import NDO_JHl_Weight39_42
import NDO_JHl_Weight43_46
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes10
open Aeneas Aeneas.Std

theorem cell40 : JHl_WeightCell.Law ⟨40,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight39_42.source40
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 40 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight40.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1352).take 16
  rw [JFq_Weight40.selected]
  exact bytes.trans (by rfl)
#print axioms cell40

theorem cell41 : JHl_WeightCell.Law ⟨41,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight39_42.source41
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 41 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight41.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1368).take 16
  rw [JFq_Weight41.selected]
  exact bytes.trans (by rfl)
#print axioms cell41

theorem cell42 : JHl_WeightCell.Law ⟨42,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight39_42.source42
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 42 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight42.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1384).take 16
  rw [JFq_Weight42.selected]
  exact bytes.trans (by rfl)
#print axioms cell42

theorem cell43 : JHl_WeightCell.Law ⟨43,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight43_46.source43
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 43 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight43.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1400).take 16
  rw [JFq_Weight43.selected]
  exact bytes.trans (by rfl)
#print axioms cell43
end AspisR1.JHl_WeightBytes10
end
