import AspisR1.PoseidonExternalLinearGroupStep
import AspisR1.PoseidonGroupSliceModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalLinearGroupModel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalRowExtensionMap
open AspisR1.PoseidonExternalLinearGroupStep
open AspisR1.PoseidonGroupSliceModel

abbrev QM := field.QM31
abbrev State := Array QM 16#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

private theorem read_value (state : State) (i : Usize) (q : QM)
    (hi : i.val < 16)
    (hread : Array.index_usize state i = .ok q) :
    q = state.val[i.val]'(by simpa [state.property] using hi) := by
  have hget : Array.index_usize state i =
      .ok (state.val[i.val]'(by simpa [state.property] using hi)) := by
    exact AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok state i hi
  exact Result.ok.inj (hread.symm.trans hget)

theorem group_step_model
    (state : State) (group : Fin 4) (q0 q1 q2 q3 : QM)
    (i0 i1 i2 i3 : Usize)
    (hread0 : Array.index_usize state i0 = .ok q0)
    (hread1 : Array.index_usize state i1 = .ok q1)
    (hread2 : Array.index_usize state i2 = .ok q2)
    (hread3 : Array.index_usize state i3 = .ok q3)
    (hindex0 : i0.val = 4 * group.val)
    (hindex1 : i1.val = 4 * group.val + 1)
    (hindex2 : i2.val = 4 * group.val + 2)
    (hindex3 : i3.val = 4 * group.val + 3)
    (hi0 : i0.val < 16) (hi1 : i1.val < 16)
    (hi2 : i2.val < 16) (hi3 : i3.val < 16) :
    ∃ v0 v1 v2 v3 : QM, ∃ s1 s2 s3 s4 : State,
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
        Array.update a2 i3 o3) = .ok s4 ∧
      s1 = state.set i0 v0 ∧ s2 = s1.set i1 v1 ∧
      s3 = s2.set i2 v2 ∧ s4 = s3.set i3 v3 ∧
      (∀ r : Fin 4, Decode (match r.val with
        | 0 => v0 | 1 => v1 | 2 => v2 | _ => v3) =
        R0P.poseidonMat4 (fun j => Decode (cell16 state group j)) r) := by
  obtain ⟨v0,v1,v2,v3,s1,s2,s3,s4,hv0,hv1,hv2,hv3,hrun,hs1,hs2,hs3,hs4⟩ :=
    group_step_after_reads state q0 q1 q2 q3 i0 i1 i2 i3
      hread0 hread1 hread2 hread3 hi0 hi1 hi2 hi3
  have hq0 := read_value state i0 q0 hi0 hread0
  have hq1 := read_value state i1 q1 hi1 hread1
  have hq2 := read_value state i2 q2 hi2 hread2
  have hq3 := read_value state i3 q3 hi3 hread3
  have hc : ∀ j : Fin 4, groupCell q0 q1 q2 q3 j = cell16 state group j := by
    intro j
    fin_cases j <;> simp [groupCell, groupInput, Array.make, cell16,
      hq0, hq1, hq2, hq3,
      hindex0, hindex1, hindex2, hindex3]
  have hv0model : Decode v0 = R0P.poseidonMat4
      (fun j => Decode (groupCell q0 q1 q2 q3 j)) (0 : Fin 4) := by
    obtain ⟨w, hcall, _, hmodel⟩ := group_row_success q0 q1 q2 q3 0#usize (by decide)
    have heq : w = v0 := Result.ok.inj (hcall.symm.trans hv0)
    have hfin : (⟨(0#usize).val, by decide⟩ : Fin 4) = (0 : Fin 4) := by
      apply Fin.ext
      simp [UScalar.ofNatCore_val_eq]
    simpa [heq, hfin] using hmodel
  have hv1model : Decode v1 = R0P.poseidonMat4
      (fun j => Decode (groupCell q0 q1 q2 q3 j)) (1 : Fin 4) := by
    obtain ⟨w, hcall, _, hmodel⟩ := group_row_success q0 q1 q2 q3 1#usize (by decide)
    have heq : w = v1 := Result.ok.inj (hcall.symm.trans hv1)
    have hfin : (⟨(1#usize).val, by decide⟩ : Fin 4) = (1 : Fin 4) := by
      apply Fin.ext
      simp [UScalar.ofNatCore_val_eq]
    simpa [heq, hfin] using hmodel
  have hv2model : Decode v2 = R0P.poseidonMat4
      (fun j => Decode (groupCell q0 q1 q2 q3 j)) (2 : Fin 4) := by
    obtain ⟨w, hcall, _, hmodel⟩ := group_row_success q0 q1 q2 q3 2#usize (by decide)
    have heq : w = v2 := Result.ok.inj (hcall.symm.trans hv2)
    have hfin : (⟨(2#usize).val, by decide⟩ : Fin 4) = (2 : Fin 4) := by
      apply Fin.ext
      simp [UScalar.ofNatCore_val_eq]
    simpa [heq, hfin] using hmodel
  have hv3model : Decode v3 = R0P.poseidonMat4
      (fun j => Decode (groupCell q0 q1 q2 q3 j)) (3 : Fin 4) := by
    obtain ⟨w, hcall, _, hmodel⟩ := group_row_success q0 q1 q2 q3 3#usize (by decide)
    have heq : w = v3 := Result.ok.inj (hcall.symm.trans hv3)
    have hfin : (⟨(3#usize).val, by decide⟩ : Fin 4) = (3 : Fin 4) := by
      apply Fin.ext
      simp [UScalar.ofNatCore_val_eq]
    simpa [heq, hfin] using hmodel
  refine ⟨v0,v1,v2,v3,s1,s2,s3,s4,hrun,hs1,hs2,hs3,hs4,?_⟩
  intro r
  fin_cases r
  · have hrow : (0 : Fin 4) = (⟨0, by omega⟩ : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hrow] at hv0model
    simpa only [hc] using hv0model
  · have hrow : (1 : Fin 4) = (⟨1, by omega⟩ : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hrow] at hv1model
    simpa only [hc] using hv1model
  · have hrow : (2 : Fin 4) = (⟨2, by omega⟩ : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hrow] at hv2model
    simpa only [hc] using hv2model
  · have hrow : (3 : Fin 4) = (⟨3, by omega⟩ : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hrow] at hv3model
    simpa only [hc] using hv3model

#print axioms group_step_model
end AspisR1.PoseidonExternalLinearGroupModel
