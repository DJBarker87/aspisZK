import R1Z.PV_CB3_WeightsSubtract
import R1Z.PV_CB3_StagedComposition
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsDenseRead
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Points := Array (Array aspis_core.field.QM31 10#usize) 3#usize

def point (points : Points) (kind b : Usize) : Result aspis_core.field.QM31 := do
  let k ← UScalar.sub kind 1#usize
  let coordinate ← UScalar.sub 9#usize b
  let row ← Array.index_usize points k
  Array.index_usize row coordinate

/-- The D branch's kind and loop tests suffice for all point-array reads. -/
theorem total (points : Points) (kind b : Usize)
    (lo : 1 ≤ kind.val) (hi : kind.val ≤ 3) (hb : b.val < 10) :
    ∃ p, point points kind b = ok p := by
  have hsub : b.val ≤ (9#usize).val := by change b.val≤9; omega
  have hk : (Usize.wrapping_sub kind 1#usize).val < 3 := by
    rw [PV_CB3_WeightsSubtract.wrapping_value kind 1#usize lo]
    change kind.val-1<3
    omega
  have hc : (Usize.wrapping_sub 9#usize b).val < 10 := by
    rw [PV_CB3_WeightsSubtract.wrapping_value 9#usize b hsub]
    change 9-b.val<10
    omega
  obtain ⟨row,hr⟩ := PV_CB3_StagedComposition.read_total points (Usize.wrapping_sub kind 1#usize) hk
  obtain ⟨p,hp⟩ := PV_CB3_StagedComposition.read_total row (Usize.wrapping_sub 9#usize b) hc
  refine ⟨p,?_⟩
  simp only [point,PV_CB3_WeightsSubtract.checked kind 1#usize lo,
    PV_CB3_WeightsSubtract.checked 9#usize b hsub,bind_tc_ok,hr,hp]
#print axioms total
end R1Z.PV_CB3_WeightsDenseRead
