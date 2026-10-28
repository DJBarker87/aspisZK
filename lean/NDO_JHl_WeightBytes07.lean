import NDO_JHl_WeightCell
import NDO_JHl_Weight27_30
import NDO_JHl_Weight31_34
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes07
open Aeneas Aeneas.Std

theorem cell28 : JHl_WeightCell.Law ⟨28,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight27_30.source28
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 28 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight28.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1160).take 16
  rw [JFq_Weight28.selected]
  exact bytes.trans (by rfl)
#print axioms cell28

theorem cell29 : JHl_WeightCell.Law ⟨29,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight27_30.source29
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 29 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight29.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1176).take 16
  rw [JFq_Weight29.selected]
  exact bytes.trans (by rfl)
#print axioms cell29

theorem cell30 : JHl_WeightCell.Law ⟨30,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight27_30.source30
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 30 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight30.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1192).take 16
  rw [JFq_Weight30.selected]
  exact bytes.trans (by rfl)
#print axioms cell30

theorem cell31 : JHl_WeightCell.Law ⟨31,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight31_34.source31
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 31 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight31.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 1208).take 16
  rw [JFq_Weight31.selected]
  exact bytes.trans (by rfl)
#print axioms cell31
end AspisR1.JHl_WeightBytes07
end
