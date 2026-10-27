import RPu_FJf_MapRead
import RPu_FJf_NativeFactors
import RPv_FJj_TensorPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_NativeRow
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)

theorem value (w : FIo_Install.W) (hc : FJf_FactorArray.canon w.factors)
    (idx : Usize) (row : Array (Array NQ 4#usize) 5#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors idx=ok row) :
    (∀ digit∈row.val,FJf_QMArray.canon digit) ∧ ∀ d s,
      FJj_TensorPrefix.rowValue row d s=FJf_FactorArray.value w.factors idx.val d s := by
  obtain ⟨sr,hsr,er⟩ := FJf_MapRead.source
    (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) w.factors idx row hr
  have cr := hc sr (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hsr))
  constructor
  · rw [←er]
    intro digit hd
    change digit∈sr.val.map (FIn_WeightsInstall.mapArray FIo_Install.toQ) at hd
    obtain ⟨sd,hsd,rfl⟩ := List.mem_map.mp hd
    intro q hq
    change q∈sd.val.map FIo_Install.toQ at hq
    obtain ⟨sq,hsq,rfl⟩ := List.mem_map.mp hq
    exact cr sd hsd sq hsq
  · intro d s
    rw [←er]
    exact (FJf_NativeFactors.row_map sr d s).trans (FJf_FactorArray.row_read w.factors idx sr hsr d s).symm

#print axioms value
end AspisR1.FJr_NativeRow
end
