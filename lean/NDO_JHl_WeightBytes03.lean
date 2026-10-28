import NDO_JHl_WeightCell
import NDO_JHl_Weight11_14
import NDO_JHl_Weight15_18
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes03
open Aeneas Aeneas.Std

theorem cell12 : JHl_WeightCell.Law ⟨12,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight11_14.source12
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 12 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight12.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 904).take 16
  rw [JFq_Weight12.selected]
  exact bytes.trans (by rfl)
#print axioms cell12

theorem cell13 : JHl_WeightCell.Law ⟨13,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight11_14.source13
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 13 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight13.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 920).take 16
  rw [JFq_Weight13.selected]
  exact bytes.trans (by rfl)
#print axioms cell13

theorem cell14 : JHl_WeightCell.Law ⟨14,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight11_14.source14
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 14 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight14.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 936).take 16
  rw [JFq_Weight14.selected]
  exact bytes.trans (by rfl)
#print axioms cell14

theorem cell15 : JHl_WeightCell.Law ⟨15,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight15_18.source15
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 15 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight15.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 952).take 16
  rw [JFq_Weight15.selected]
  exact bytes.trans (by rfl)
#print axioms cell15
end AspisR1.JHl_WeightBytes03
end
