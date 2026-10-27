import FJf_OriginalCanon
import FJf_MapRead
import FJf_QMArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_OriginalDigitCanon
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)

theorem value (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (d : Usize) (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok row)
    (hd : Array.index_usize row d=ok digit) : FJf_QMArray.canon digit := by
  obtain ⟨sr,hsr,er⟩ := FJf_MapRead.source
    (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) w.factors 0#usize row hr
  subst row
  obtain ⟨sd,hsd,ed⟩ := FJf_MapRead.source (FIn_WeightsInstall.mapArray FIo_Install.toQ) sr d digit hd
  have cr := FJf_OriginalCanon.installed .S2 alpha z w hc hw sr
    (by simpa only [show (0#usize).val=0 from by decide] using FJc_ReadSlot.slot _ _ _ hsr)
  have cd := cr sd (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hsd))
  rw [←ed]
  intro q hq
  change q∈sd.val.map FIo_Install.toQ at hq
  obtain ⟨sq,hsq,rfl⟩ := List.mem_map.mp hq
  exact cd sq hsq
#print axioms value
end AspisR1.FJg_OriginalDigitCanon
end
