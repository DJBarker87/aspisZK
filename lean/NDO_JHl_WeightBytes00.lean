import NDO_JHl_WeightCell
import NDO_JHl_Weight00
import NDO_JHl_Weight01_02
import NDO_JHl_Weight03_06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightBytes00
open Aeneas Aeneas.Std

theorem cell00 : JHl_WeightCell.Law ⟨0,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight00.source
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 0 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight00.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 712).take 16
  rw [JFq_Weight00.selected]
  exact bytes.trans (by rfl)
#print axioms cell00

theorem cell01 : JHl_WeightCell.Law ⟨1,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight01_02.source01
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 1 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight01.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 728).take 16
  rw [JFq_Weight01.selected]
  exact bytes.trans (by rfl)
#print axioms cell01

theorem cell02 : JHl_WeightCell.Law ⟨2,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight01_02.source02
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 2 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight02.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 744).take 16
  rw [JFq_Weight02.selected]
  exact bytes.trans (by rfl)
#print axioms cell02

theorem cell03 : JHl_WeightCell.Law ⟨3,by decide⟩ := by
  intro q canonical same
  have numeric := JHl_Weight03_06.source03
  change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 3 at same
  rw [numeric] at same
  have bytes := JHl_WeightCell.equal q JFq_Weight03.scalar canonical
    (by unfold Port3_FlushInstall.Canonical;decide) same
  rw [JHk_PreparedScalarBytes.encodeK] at bytes
  change JHl_WeightCell.encoded q=(JFx_NativeBytes.checkpoint.val.drop 760).take 16
  rw [JFq_Weight03.selected]
  exact bytes.trans (by rfl)
#print axioms cell03
end AspisR1.JHl_WeightBytes00
end
