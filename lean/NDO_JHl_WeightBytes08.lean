import NDO_JHl_WeightCell
import NDO_JHl_Weight31_34
import NDO_JHl_Weight35_38
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes08
open Aeneas Aeneas.Std

theorem cell32 : JHl_WeightCell.Law ⟨32,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight31_34.source32
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 32 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight32.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1224).take 16
  rw [JFq_Weight32.selected]
  exact bytes.trans (by rfl)
#print axioms cell32

theorem cell33 : JHl_WeightCell.Law ⟨33,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight31_34.source33
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 33 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight33.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1240).take 16
  rw [JFq_Weight33.selected]
  exact bytes.trans (by rfl)
#print axioms cell33

theorem cell34 : JHl_WeightCell.Law ⟨34,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight31_34.source34
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 34 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight34.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1256).take 16
  rw [JFq_Weight34.selected]
  exact bytes.trans (by rfl)
#print axioms cell34

theorem cell35 : JHl_WeightCell.Law ⟨35,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight35_38.source35
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 35 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight35.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1272).take 16
  rw [JFq_Weight35.selected]
  exact bytes.trans (by rfl)
#print axioms cell35
end AspisR1.JHl_WeightBytes08
end
