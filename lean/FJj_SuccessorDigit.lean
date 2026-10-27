import FJj_SuccessorInstalled
import FJg_OriginalDigitValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorDigit
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)

theorem value (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (d : Usize) (hd : d.val<5) (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 1#usize=ok row)
    (hdi : Array.index_usize row d=ok digit) :
    FJf_QMArray.canon digit ∧ ∀ s : Fin 4,FJf_QMArray.value digit s.val=
      FJd_PointReference.pointFactors
        (R0P.SemSource.successorPoint (FJf_ModelPoint.decoded
          (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))) ⟨d.val,hd⟩ s := by
  obtain ⟨sr,hsr,er⟩ := FJf_MapRead.source
    (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) w.factors 1#usize row hr
  subst row
  obtain ⟨sd,hsd,ed⟩ := FJf_MapRead.source (FIn_WeightsInstall.mapArray FIo_Install.toQ) sr d digit hdi
  have sv := FJj_SuccessorInstalled.value .S2 alpha z w hc hw
  have cr := sv.1 sr (by simpa only [show (1#usize).val=1 from by decide] using FJc_ReadSlot.slot _ _ _ hsr)
  have cd := cr sd (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hsd))
  constructor
  · rw [←ed]
    intro q hq
    change q∈sd.val.map FIo_Install.toQ at hq
    obtain ⟨sq,hsq,rfl⟩ := List.mem_map.mp hq
    exact cd sq hsq
  · intro s
    have hv := sv.2 ⟨d.val,hd⟩ s
    have rv := FJf_FactorArray.row_read w.factors 1#usize sr hsr d.val s.val
    simp only [show (1#usize).val=1 from by decide] at rv
    rw [rv] at hv
    unfold FJf_FactorArray.rowValue at hv
    simp only [FJc_ReadSlot.slot _ _ _ hsd] at hv
    rw [←ed]
    exact (FJf_NativeFactors.digit_map sd s.val).trans hv
#print axioms value
end AspisR1.FJj_SuccessorDigit
end
