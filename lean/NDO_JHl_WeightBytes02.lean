import NDO_JHl_WeightCell
import NDO_JHl_Weight07_10
import NDO_JHl_Weight11_14
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes02
open Aeneas Aeneas.Std

theorem cell08 : JHl_WeightCell.Law ⟨8,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight07_10.source08
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 8 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight08.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 840).take 16
  rw [JFq_Weight08.selected]
  exact bytes.trans (by rfl)
#print axioms cell08

theorem cell09 : JHl_WeightCell.Law ⟨9,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight07_10.source09
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 9 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight09.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 856).take 16
  rw [JFq_Weight09.selected]
  exact bytes.trans (by rfl)
#print axioms cell09

theorem cell10 : JHl_WeightCell.Law ⟨10,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight07_10.source10
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 10 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight10.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 872).take 16
  rw [JFq_Weight10.selected]
  exact bytes.trans (by rfl)
#print axioms cell10

theorem cell11 : JHl_WeightCell.Law ⟨11,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight11_14.source11
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 11 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight11.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 888).take 16
  rw [JFq_Weight11.selected]
  exact bytes.trans (by rfl)
#print axioms cell11
end AspisR1.JHl_WeightBytes02
end
