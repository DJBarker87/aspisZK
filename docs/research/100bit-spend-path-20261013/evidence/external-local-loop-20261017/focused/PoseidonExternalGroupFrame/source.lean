import PoseidonExternalGroupUpdateCells
import PoseidonExternalLinearGroupModelV6
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalGroupFrame
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalGroupUpdateCells
open AspisR1.PoseidonExternalLinearGroupModel
abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31

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

theorem four_updates_frame
    (state s1 s2 s3 s4 : State) (group : Fin 4)
    (v0 v1 v2 v3 : QM) (i0 i1 i2 i3 : Usize)
    (hs1 : s1 = state.set i0 v0) (hs2 : s2 = s1.set i1 v1)
    (hs3 : s3 = s2.set i2 v2) (hs4 : s4 = s3.set i3 v3)
    (hindex0 : i0.val = 4 * group.val)
    (hindex1 : i1.val = 4 * group.val + 1)
    (hindex2 : i2.val = 4 * group.val + 2)
    (hindex3 : i3.val = 4 * group.val + 3)
    (hi0 : i0.val < 16) (hi1 : i1.val < 16)
    (hi2 : i2.val < 16) (hi3 : i3.val < 16)
    (j : Fin 16)
    (hframe : ∀ r : Fin 4, j.val ≠ 4 * group.val + r.val) :
    cellAt s4 j.val = cellAt state j.val := by
  rw [hs4]
  rw [cellAt_set s3 i3 v3 hi3 j.val]
  rw [hs3]
  rw [cellAt_set s2 i2 v2 hi2 j.val]
  rw [hs2]
  rw [cellAt_set s1 i1 v1 hi1 j.val]
  rw [hs1]
  rw [cellAt_set state i0 v0 hi0 j.val]
  rw [hindex0, hindex1, hindex2, hindex3]
  have h0 : j.val ≠ 4 * group.val := hframe 0
  have h1 : j.val ≠ 4 * group.val + 1 := by simpa using hframe 1
  have h2 : j.val ≠ 4 * group.val + 2 := by simpa using hframe 2
  have h3 : j.val ≠ 4 * group.val + 3 := by simpa using hframe 3
  simp [h0, h1, h2, h3]

#print axioms four_updates_frame
end AspisR1.PoseidonExternalGroupFrame
