import R1Z.PV_CB3_WeightsTensorIndex
import R1Z.PV_CB3_WeightsCount
import R1Z.PV_CB3_WeightsMachineRow
import R1Z.PV_CB3_StagedComposition
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsTensorRead
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Factors := Array (Array (Array aspis_core.field.QM31 4#usize) 5#usize) 5#usize

def read (factors : Factors) (kind j d : Usize) : Result aspis_core.field.QM31 := do
  let k ← if kind < 4#usize then UScalar.sub kind 1#usize else UScalar.sub kind 2#usize
  let plane ← Array.index_usize factors k
  let line ← Array.index_usize plane d
  Array.index_usize line (PV_CB3_WeightsMachineRow.digit j (PV_CB3_WeightsCount.count d))

/-- Input-domain helper for the tensor loop, with arbitrary factor values. -/
theorem total (factors : Factors) (kind j d : Usize)
    (lo : 1 ≤ kind.val) (hi : kind.val < 7) (hd : d.val < 5) : ∃ v, read factors kind j d = ok v := by
  obtain ⟨plane,hp⟩ := PV_CB3_StagedComposition.read_total factors (PV_CB3_WeightsTensorIndex.index kind)
    (PV_CB3_WeightsTensorIndex.bound kind lo hi)
  obtain ⟨line,hl⟩ := PV_CB3_StagedComposition.read_total plane d hd
  obtain ⟨v,hv⟩ := PV_CB3_StagedComposition.read_total line
    (PV_CB3_WeightsMachineRow.digit j (PV_CB3_WeightsCount.count d))
    (PV_CB3_WeightsMachineRow.digit_bound j _ (PV_CB3_WeightsCount.bound d hd))
  refine ⟨v,?_⟩
  simp only [read,PV_CB3_WeightsTensorIndex.checked kind lo,bind_tc_ok,hp,hl,hv]
#print axioms total
end R1Z.PV_CB3_WeightsTensorRead
