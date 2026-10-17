import AspisR1.PoseidonExternalLinearGroupStep
import AspisR1.PoseidonFullRoundCellStep

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalGroupCanonical
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalRowExtensionMap
open AspisR1.PoseidonExternalLinearGroupStep
open AspisR1.PoseidonFullRoundCellStep

abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

theorem group_step_after_reads_canonical
    (state : State) (q0 q1 q2 q3 : QM) (i0 i1 i2 i3 : Usize)
    (hread0 : Array.index_usize state i0 = .ok q0)
    (hread1 : Array.index_usize state i1 = .ok q1)
    (hread2 : Array.index_usize state i2 = .ok q2)
    (hread3 : Array.index_usize state i3 = .ok q3)
    (hi0 : i0.val < 16) (hi1 : i1.val < 16)
    (hi2 : i2.val < 16) (hi3 : i3.val < 16)
    (hstate : CanonicalState state) :
    ∃ out : State,
      (do
        let x0 ← Array.index_usize state i0
        let x1 ← Array.index_usize state i1
        let x2 ← Array.index_usize state i2
        let x3 ← Array.index_usize state i3
        let input ← core.array.Array.map
          (BuiltinFnMut QM (Array Std.U32 4#usize))
          (Array.make 4#usize [x0,x1,x2,x3])
          state_only_poseidon.extension_limbs
        let o0 ← state_only_poseidon.external_linear_lazy_row input 0#usize
        let a0 ← Array.update state i0 o0
        let o1 ← state_only_poseidon.external_linear_lazy_row input 1#usize
        let a1 ← Array.update a0 i1 o1
        let o2 ← state_only_poseidon.external_linear_lazy_row input 2#usize
        let a2 ← Array.update a1 i2 o2
        let o3 ← state_only_poseidon.external_linear_lazy_row input 3#usize
        Array.update a2 i3 o3) = .ok out ∧
      CanonicalState out := by
  obtain ⟨v0,v1,v2,v3,s1,s2,s3,s4,hv0,hv1,hv2,hv3,hrun,hs1,hs2,hs3,hs4⟩ :=
    group_step_after_reads state q0 q1 q2 q3 i0 i1 i2 i3
      hread0 hread1 hread2 hread3 hi0 hi1 hi2 hi3
  obtain ⟨w0,hw0,hcan0,_⟩ := group_row_success q0 q1 q2 q3 0#usize (by decide)
  obtain ⟨w1,hw1,hcan1,_⟩ := group_row_success q0 q1 q2 q3 1#usize (by decide)
  obtain ⟨w2,hw2,hcan2,_⟩ := group_row_success q0 q1 q2 q3 2#usize (by decide)
  obtain ⟨w3,hw3,hcan3,_⟩ := group_row_success q0 q1 q2 q3 3#usize (by decide)
  have heq0 : w0 = v0 := Result.ok.inj (hw0.symm.trans hv0)
  have heq1 : w1 = v1 := Result.ok.inj (hw1.symm.trans hv1)
  have heq2 : w2 = v2 := Result.ok.inj (hw2.symm.trans hv2)
  have heq3 : w3 = v3 := Result.ok.inj (hw3.symm.trans hv3)
  have hcan0v : Canonical v0 := heq0 ▸ hcan0
  have hcan1v : Canonical v1 := heq1 ▸ hcan1
  have hcan2v : Canonical v2 := heq2 ▸ hcan2
  have hcan3v : Canonical v3 := heq3 ▸ hcan3
  have hs1can : CanonicalState s1 := by rw [hs1]; exact set_canonical state i0 v0 hstate hcan0v
  have hs2can : CanonicalState s2 := by rw [hs2]; exact set_canonical s1 i1 v1 hs1can hcan1v
  have hs3can : CanonicalState s3 := by rw [hs3]; exact set_canonical s2 i2 v2 hs2can hcan2v
  have hs4can : CanonicalState s4 := by rw [hs4]; exact set_canonical s3 i3 v3 hs3can hcan3v
  exact ⟨s4,hrun,hs4can⟩

#print axioms group_step_after_reads_canonical
end AspisR1.PoseidonExternalGroupCanonical
