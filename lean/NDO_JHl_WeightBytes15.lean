import NDO_JHl_WeightCell
import NDO_JHl_Weight59_62
import NDO_JHl_Weight63_63
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes15
open Aeneas Aeneas.Std

theorem cell60 : JHl_WeightCell.Law ⟨60,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight59_62.source60
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 60 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight60.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1672).take 16
  rw [JFq_Weight60.selected]
  exact bytes.trans (by rfl)
#print axioms cell60

theorem cell61 : JHl_WeightCell.Law ⟨61,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight59_62.source61
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 61 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight61.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1688).take 16
  rw [JFq_Weight61.selected]
  exact bytes.trans (by rfl)
#print axioms cell61

theorem cell62 : JHl_WeightCell.Law ⟨62,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight59_62.source62
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 62 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight62.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1704).take 16
  rw [JFq_Weight62.selected]
  exact bytes.trans (by rfl)
#print axioms cell62

theorem cell63 : JHl_WeightCell.Law ⟨63,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight63_63.source63
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 63 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight63.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1720).take 16
  rw [JFq_Weight63.selected]
  exact bytes.trans (by rfl)
#print axioms cell63
end AspisR1.JHl_WeightBytes15
end
