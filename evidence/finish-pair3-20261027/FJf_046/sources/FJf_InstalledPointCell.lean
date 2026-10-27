import FJf_OriginalCanon
import FJf_MapRead
import FJf_NativeFactors
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_InstalledPointCell
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ qm)

theorem value (v : transport.Variant) (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights v alpha z=ok (.Ok w))
    (d s : Usize) (hd : d.val < 5) (hs : s.val < 4)
    (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize) (q : NQ)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok row)
    (hdi : Array.index_usize row d=ok digit) (hsi : Array.index_usize digit s=ok q) :
    FIo_QMValues.Canon q ∧ decodeQM (qm q)=
      FJf_PointCell.point (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha)
        d.val ⟨s.val,hs⟩ := by
  obtain ⟨sr,hsr,er⟩ := FJf_MapRead.source
    (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) w.factors 0#usize row hr
  subst row
  obtain ⟨sd,hsd,ed⟩ := FJf_MapRead.source (FIn_WeightsInstall.mapArray FIo_Install.toQ) sr d digit hdi
  subst digit
  obtain ⟨sq,hsq,eq⟩ := FJf_MapRead.source FIo_Install.toQ sd s q hsi
  have cr := FJf_OriginalCanon.installed v alpha z w hc hw sr
    (by simpa only [show (0#usize).val=0 from by decide] using FJc_ReadSlot.slot _ _ _ hsr)
  have cd := cr sd (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hsd))
  have cq := FJc_WeightArray.canonical_read sd s sq cd hsq
  have hv := FJf_OriginalFactors.installed v alpha z w hc hw ⟨d.val,hd⟩ ⟨s.val,hs⟩
  have rv := FJf_FactorArray.row_read w.factors 0#usize sr hsr d.val s.val
  rw [rv] at hv
  unfold FJf_FactorArray.rowValue at hv
  rw [FJc_ReadSlot.slot _ _ _ hsd,FJc_WeightArray.read sd s sq hsq] at hv
  rw [←eq]
  exact ⟨cq,hv⟩
#print axioms value
end AspisR1.FJf_InstalledPointCell
end
