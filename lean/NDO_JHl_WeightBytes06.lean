import NDO_JHl_WeightCell
import NDO_JHl_Weight23_26
import NDO_JHl_Weight27_30
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes06
open Aeneas Aeneas.Std

theorem cell24 : JHl_WeightCell.Law ⟨24,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight23_26.source24
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 24 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight24.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1096).take 16
  rw [JFq_Weight24.selected]
  exact bytes.trans (by rfl)
#print axioms cell24

theorem cell25 : JHl_WeightCell.Law ⟨25,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight23_26.source25
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 25 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight25.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1112).take 16
  rw [JFq_Weight25.selected]
  exact bytes.trans (by rfl)
#print axioms cell25

theorem cell26 : JHl_WeightCell.Law ⟨26,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight23_26.source26
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 26 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight26.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1128).take 16
  rw [JFq_Weight26.selected]
  exact bytes.trans (by rfl)
#print axioms cell26

theorem cell27 : JHl_WeightCell.Law ⟨27,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight27_30.source27
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 27 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight27.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1144).take 16
  rw [JFq_Weight27.selected]
  exact bytes.trans (by rfl)
#print axioms cell27
end AspisR1.JHl_WeightBytes06
end
