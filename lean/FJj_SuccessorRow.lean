import FJj_SuccessorInstalled
import FJf_MapRead
import FJf_QMArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorRow
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)

theorem value (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (row : Array (Array NQ 4#usize) 5#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 1#usize=ok row) :
    ∀ digit∈row.val,FJf_QMArray.canon digit := by
  obtain ⟨sr,hsr,er⟩ := FJf_MapRead.source
    (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) w.factors 1#usize row hr
  have source := FJj_SuccessorInstalled.value .S2 alpha z w hc hw
  have canon := source.1 sr (by simpa only [show (1#usize).val=1 from by decide] using FJc_ReadSlot.slot _ _ _ hsr)
  rw [←er]
  intro digit hd
  change digit∈sr.val.map (FIn_WeightsInstall.mapArray FIo_Install.toQ) at hd
  obtain ⟨sd,hsd,rfl⟩ := List.mem_map.mp hd
  intro q hq
  change q∈sd.val.map FIo_Install.toQ at hq
  obtain ⟨sq,hsq,rfl⟩ := List.mem_map.mp hq
  exact canon sd hsd sq hsq
#print axioms value
end AspisR1.FJj_SuccessorRow
end
