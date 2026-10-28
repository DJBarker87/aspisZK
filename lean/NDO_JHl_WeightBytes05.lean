import NDO_JHl_WeightCell
import NDO_JHl_Weight19_22
import NDO_JHl_Weight23_26
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes05
open Aeneas Aeneas.Std

theorem cell20 : JHl_WeightCell.Law ⟨20,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight19_22.source20
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 20 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight20.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1032).take 16
  rw [JFq_Weight20.selected]
  exact bytes.trans (by rfl)
#print axioms cell20

theorem cell21 : JHl_WeightCell.Law ⟨21,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight19_22.source21
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 21 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight21.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1048).take 16
  rw [JFq_Weight21.selected]
  exact bytes.trans (by rfl)
#print axioms cell21

theorem cell22 : JHl_WeightCell.Law ⟨22,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight19_22.source22
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 22 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight22.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1064).take 16
  rw [JFq_Weight22.selected]
  exact bytes.trans (by rfl)
#print axioms cell22

theorem cell23 : JHl_WeightCell.Law ⟨23,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight23_26.source23
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 23 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight23.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1080).take 16
  rw [JFq_Weight23.selected]
  exact bytes.trans (by rfl)
#print axioms cell23
end AspisR1.JHl_WeightBytes05
end
