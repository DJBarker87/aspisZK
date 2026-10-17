import PoseidonExternalLinearGroupModelV6

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalGroupUpdateCells
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLinearGroupModel
open AspisR1.PoseidonGroupSliceModel

abbrev QM := field.QM31
abbrev State := Array QM 16#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

def cellAt (a : State) (j : Nat) : QM :=
  if h : j < 16 then a.val[j]'(by simpa [a.property] using h) else field.QM31.ZERO

private theorem cellAt_set (a : State) (i : Usize) (x : QM)
    (hi : i.val < 16) (j : Nat) :
    cellAt (a.set i x) j = if j = i.val then x else cellAt a j := by
  by_cases hj : j < 16
  · by_cases heq : j = i.val
    · subst j
      simp [cellAt, hj, Array.set_val_eq]
    · have hne : i.val ≠ j := Ne.symm heq
      have hjSet : j < (a.val.set i.val x).length := by simpa [a.property] using hj
      have hjA : j < a.val.length := by simpa [a.property] using hj
      have hcell := List.getElem_set_ne (l := a.val) (i := i.val)
        (j := j) hne hjSet
      simp [cellAt, hj, Array.set_val_eq, heq, hcell, hjA]
  · have hne : j ≠ i.val := by omega
    simp [cellAt, hj, Array.set_val_eq, hne]

theorem group_step_cell_values
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
      ∀ j : Fin 4,
        Decode (cellAt out (4 * group.val + j.val)) =
          R0P.poseidonMat4 (fun k => Decode (cell16 state group k)) j := by
  obtain ⟨v0,v1,v2,v3,s1,s2,s3,s4,hrun,hs1,hs2,hs3,hs4,hmodel⟩ :=
    group_step_model state group q0 q1 q2 q3 i0 i1 i2 i3
      hread0 hread1 hread2 hread3 hindex0 hindex1 hindex2 hindex3
      hi0 hi1 hi2 hi3
  have hget0 : cellAt s4 (4 * group.val) = v0 := by
    rw [hs4]
    rw [cellAt_set s3 i3 v3 hi3 (4 * group.val)]
    rw [hs3]
    rw [cellAt_set s2 i2 v2 hi2 (4 * group.val)]
    rw [hs2]
    rw [cellAt_set s1 i1 v1 hi1 (4 * group.val)]
    rw [hs1]
    rw [cellAt_set state i0 v0 hi0 (4 * group.val)]
    rw [hindex0, hindex1, hindex2, hindex3]
    simp <;> omega
  have hget1 : cellAt s4 (4 * group.val + 1) = v1 := by
    rw [hs4]
    rw [cellAt_set s3 i3 v3 hi3 (4 * group.val + 1)]
    rw [hs3]
    rw [cellAt_set s2 i2 v2 hi2 (4 * group.val + 1)]
    rw [hs2]
    rw [cellAt_set s1 i1 v1 hi1 (4 * group.val + 1)]
    rw [hs1]
    rw [cellAt_set state i0 v0 hi0 (4 * group.val + 1)]
    rw [hindex0, hindex1, hindex2, hindex3]
    simp <;> omega
  have hget2 : cellAt s4 (4 * group.val + 2) = v2 := by
    rw [hs4]
    rw [cellAt_set s3 i3 v3 hi3 (4 * group.val + 2)]
    rw [hs3]
    rw [cellAt_set s2 i2 v2 hi2 (4 * group.val + 2)]
    rw [hs2]
    rw [cellAt_set s1 i1 v1 hi1 (4 * group.val + 2)]
    rw [hs1]
    rw [cellAt_set state i0 v0 hi0 (4 * group.val + 2)]
    rw [hindex0, hindex1, hindex2, hindex3]
    simp <;> omega
  have hget3 : cellAt s4 (4 * group.val + 3) = v3 := by
    rw [hs4]
    rw [cellAt_set s3 i3 v3 hi3 (4 * group.val + 3)]
    rw [hs3]
    rw [cellAt_set s2 i2 v2 hi2 (4 * group.val + 3)]
    rw [hs2]
    rw [cellAt_set s1 i1 v1 hi1 (4 * group.val + 3)]
    rw [hs1]
    rw [cellAt_set state i0 v0 hi0 (4 * group.val + 3)]
    rw [hindex0, hindex1, hindex2, hindex3]
    simp <;> omega
  refine ⟨s4, hrun, ?_⟩
  intro j
  fin_cases j
  · simpa [hget0] using hmodel (0 : Fin 4)
  · simpa [hget1] using hmodel (1 : Fin 4)
  · simpa [hget2] using hmodel (2 : Fin 4)
  · simpa [hget3] using hmodel (3 : Fin 4)

#print axioms group_step_cell_values
end AspisR1.PoseidonExternalGroupUpdateCells
