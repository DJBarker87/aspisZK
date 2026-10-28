import NDO_JHl_WeightCell
import NDO_JHl_Weight15_18
import NDO_JHl_Weight19_22
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes04
open Aeneas Aeneas.Std

theorem cell16 : JHl_WeightCell.Law ⟨16,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight15_18.source16
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 16 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight16.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 968).take 16
  rw [JFq_Weight16.selected]
  exact bytes.trans (by rfl)
#print axioms cell16

theorem cell17 : JHl_WeightCell.Law ⟨17,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight15_18.source17
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 17 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight17.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 984).take 16
  rw [JFq_Weight17.selected]
  exact bytes.trans (by rfl)
#print axioms cell17

theorem cell18 : JHl_WeightCell.Law ⟨18,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight15_18.source18
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 18 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight18.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1000).take 16
  rw [JFq_Weight18.selected]
  exact bytes.trans (by rfl)
#print axioms cell18

theorem cell19 : JHl_WeightCell.Law ⟨19,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight19_22.source19
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 19 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight19.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1016).take 16
  rw [JFq_Weight19.selected]
  exact bytes.trans (by rfl)
#print axioms cell19
end AspisR1.JHl_WeightBytes04
end
