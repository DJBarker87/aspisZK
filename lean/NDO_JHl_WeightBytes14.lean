import NDO_JHl_WeightCell
import NDO_JHl_Weight55_58
import NDO_JHl_Weight59_62
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes14
open Aeneas Aeneas.Std

theorem cell56 : JHl_WeightCell.Law ⟨56,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight55_58.source56
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 56 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight56.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1608).take 16
  rw [JFq_Weight56.selected]
  exact bytes.trans (by rfl)
#print axioms cell56

theorem cell57 : JHl_WeightCell.Law ⟨57,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight55_58.source57
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 57 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight57.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1624).take 16
  rw [JFq_Weight57.selected]
  exact bytes.trans (by rfl)
#print axioms cell57

theorem cell58 : JHl_WeightCell.Law ⟨58,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight55_58.source58
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 58 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight58.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1640).take 16
  rw [JFq_Weight58.selected]
  exact bytes.trans (by rfl)
#print axioms cell58

theorem cell59 : JHl_WeightCell.Law ⟨59,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight59_62.source59
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 59 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight59.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1656).take 16
  rw [JFq_Weight59.selected]
  exact bytes.trans (by rfl)
#print axioms cell59
end AspisR1.JHl_WeightBytes14
end
