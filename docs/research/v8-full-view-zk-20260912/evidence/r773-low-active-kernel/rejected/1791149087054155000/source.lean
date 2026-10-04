import AspisV8R19.R738JointObservationModel
namespace AspisV8R19.R773LowActiveKernel
open AspisV8R17
open R698ActiveCoreLayout
open R707FullActiveDeterminant
noncomputable section

/-- Index-only bound for the small lower normalization region. -/
theorem low_targets_bound : ∀ j : Fin 46,
    (indexTargets j.val).all (fun r => decide (r < 48)) = true := by decide

theorem low_twice_targets_bound : ∀ j : Fin 46,
    ((indexTargets j.val).flatMap indexTargets).all (fun r => decide (r < 48)) = true := by decide

theorem no_active_below_96 (j : Fin 96) :
    (⟨j.val, by omega⟩ : Fin 1024) ∉ activeCode := by
  revert j
  decide

theorem rowCode_ge_96 (j : R738JointObservationModel.J) : 96 ≤ rowCode j := by
  rcases j with i | u
  · have ha : i.val ∈ activeCode := (Finset.mem_filter.mp i.property).1
    by_contra hn
    have hi : i.val.val < 96 := by change 96 ≤ i.val.val at hn; omega
    exact no_active_below_96 ⟨i.val.val,hi⟩ (by simpa using ha)
  · change 96 ≤ 1022
    decide

variable {F : Type*} [CommRing F]

theorem low_even_support_absent (j : Fin 46) (r : Nat) (hr : 96 ≤ r) :
    ¬evenUnitSupport j.val r := by
  have hbound := low_targets_bound j
  rw [List.all_eq_true] at hbound
  have hquot : 48 ≤ r/2 := by omega
  rintro (heq | ⟨hp, hm⟩)
  · have hj := j.isLt
    omega
  · have h := of_decide_eq_true (hbound (r/2) hm)
    omega

theorem low_odd_support_absent (j : Fin 46) (r : Nat) (hr : 96 ≤ r) :
    ¬oddUnitSupport j.val r := by
  have hb := low_targets_bound j
  have hbb := low_twice_targets_bound j
  rw [List.all_eq_true] at hb hbb
  have hquot : 48 ≤ r/2 := by omega
  rintro (heq | hs)
  · have hj := j.isLt
    omega
  · by_cases hp : r%2=0
    · simp only [if_pos hp] at hs
      have h := of_decide_eq_true (hbb (r/2) hs)
      omega
    · simp only [if_neg hp] at hs
      have h := of_decide_eq_true (hb (r/2) hs)
      omega

theorem sourceChord_unit_low_zero (half a b c : F) (n : Fin 92) (r : Nat)
    (hr : 96 ≤ r) : sourceChord half (unitVector n.val) a b c r = 0 := by
  let j : Fin 46 := ⟨n.val/2,by have hn := n.isLt; omega⟩
  by_cases hp : n.val%2=0
  · have hn : n.val=2*j.val := by dsimp [j]; omega
    rw [hn]
    exact sourceChord_even_zero half j.val r (by have hj := j.isLt; omega)
      (low_even_support_absent j r hr) a b c
  · have hn : n.val=2*j.val+1 := by
      have hm := Nat.mod_lt n.val (by decide : 0<2)
      dsimp [j]
      omega
    rw [hn]
    exact sourceChord_odd_zero half j.val r (by have hj := j.isLt; omega)
      (low_odd_support_absent j r hr) a b c

theorem sourceChord_low_pair_zero (half a b c alpha : F) (d : Fin 23) (s : Fin 3)
    (r : Nat) (hr : 96 ≤ r) :
    sourceChord half (R738JointObservationModel.qPair alpha ⟨d.val,by omega⟩ s) a b c r = 0 := by
  unfold R738JointObservationModel.qPair
  rw [sourceChord_difference]
  rw [sourceChord_unit_low_zero half a b c ⟨4*d.val+s.val+1,by omega⟩ r hr,
    sourceChord_unit_low_zero half a b c ⟨4*d.val,by omega⟩ r hr]
  simp

theorem sourceChord_low_direction_zero (half a b c alpha : F) (d : Fin 23) (s : Fin 3)
    (r : Nat) (hr : 96 ≤ r) :
    sourceChord half (R738JointObservationModel.direction alpha ⟨d.val,by omega⟩ s) a b c r = 0 := by
  unfold R738JointObservationModel.direction
  change sourceChord half (fun i => R738JointObservationModel.qPair alpha ⟨d.val,by omega⟩ s i -
    1*R738JointObservationModel.qPair alpha 0 s i) a b c r = 0
  rw [sourceChord_difference,sourceChord_low_pair_zero half a b c alpha d s r hr,
    sourceChord_low_pair_zero half a b c alpha 0 s r hr]
  simp

theorem low_active_observation_zero (half a b c alpha : F) (d : Fin 23) (s : Fin 3)
    (j : R738JointObservationModel.J) :
    sourceChord half (R738JointObservationModel.direction alpha ⟨d.val,by omega⟩ s)
      a b c (rowCode j) = 0 :=
  sourceChord_low_direction_zero half a b c alpha d s (rowCode j) (rowCode_ge_96 j)

#print axioms low_targets_bound
#print axioms low_twice_targets_bound
#print axioms no_active_below_96
#print axioms rowCode_ge_96
#print axioms low_even_support_absent
#print axioms low_odd_support_absent
#print axioms sourceChord_unit_low_zero
#print axioms sourceChord_low_pair_zero
#print axioms sourceChord_low_direction_zero
#print axioms low_active_observation_zero
end
end AspisV8R19.R773LowActiveKernel
