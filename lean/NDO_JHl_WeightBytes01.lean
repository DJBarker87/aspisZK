import NDO_JHl_WeightCell
import NDO_JHl_Weight03_06
import NDO_JHl_Weight07_10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes01
open Aeneas Aeneas.Std

theorem cell04 : JHl_WeightCell.Law ⟨4,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight03_06.source04
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 4 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight04.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 776).take 16
  rw [JFq_Weight04.selected]
  exact bytes.trans (by rfl)
#print axioms cell04

theorem cell05 : JHl_WeightCell.Law ⟨5,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight03_06.source05
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 5 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight05.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 792).take 16
  rw [JFq_Weight05.selected]
  exact bytes.trans (by rfl)
#print axioms cell05

theorem cell06 : JHl_WeightCell.Law ⟨6,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight03_06.source06
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 6 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight06.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 808).take 16
  rw [JFq_Weight06.selected]
  exact bytes.trans (by rfl)
#print axioms cell06

theorem cell07 : JHl_WeightCell.Law ⟨7,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight07_10.source07
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 7 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight07.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 824).take 16
  rw [JFq_Weight07.selected]
  exact bytes.trans (by rfl)
#print axioms cell07
end AspisR1.JHl_WeightBytes01
end
