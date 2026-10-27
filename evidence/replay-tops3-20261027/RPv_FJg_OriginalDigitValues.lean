import RPu_FJf_QMArray
import RPu_FJf_InstalledPointCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_OriginalDigitValues
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)

theorem value (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (d : Usize) (hd : d.val < 5) (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok row)
    (hdi : Array.index_usize row d=ok digit) (s : Fin 4) :
    FJf_QMArray.value digit s.val=
      FJf_PointCell.point (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) d.val s := by
  obtain ⟨sr,hsr,er⟩ := FJf_MapRead.source
    (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) w.factors 0#usize row hr
  subst row
  obtain ⟨sd,hsd,ed⟩ := FJf_MapRead.source (FIn_WeightsInstall.mapArray FIo_Install.toQ) sr d digit hdi
  have hv := FJf_OriginalFactors.installed .S2 semAlpha z w hc hw ⟨d.val,hd⟩ s
  have rv := FJf_FactorArray.row_read w.factors 0#usize sr hsr d.val s.val
  dsimp only at hv
  simp only [show (0#usize).val=0 from by decide] at rv
  rw [rv] at hv
  unfold FJf_FactorArray.rowValue at hv
  simp only [FJc_ReadSlot.slot _ _ _ hsd] at hv
  rw [←ed]
  exact (FJf_NativeFactors.digit_map sd s.val).trans hv
#print axioms value
end AspisR1.FJg_OriginalDigitValues
end
