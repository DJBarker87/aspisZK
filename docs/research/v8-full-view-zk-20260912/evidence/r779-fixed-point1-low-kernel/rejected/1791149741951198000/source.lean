import AspisV8R19.R777GatherConstantOnTargets
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R776LowPoint1Transport
import AspisV8R19.R748JointWitnessPointEntry

/-! The fixed point-one witness has a constant low transported gather kernel. -/
set_option autoImplicit false
namespace AspisV8R19.R779FixedPoint1LowKernel

open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R777GatherConstantOnTargets
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R776LowPoint1Transport
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R740SparsePointObservation
noncomputable section

abbrev M := R748JointWitnessPointEntry.M
def half : M := 1073741824

theorem half_add_half : half + half = 1 := by decide

def we : Nat → M := zeroExtend 512 (fun i => w (2 * i))
def wo : Nat → M := zeroExtend 512 (fun i => w (2 * i + 1))

theorem low_even_value (j : Fin 46) : we j.val = 576 := by
  unfold we zeroExtend
  rw [if_pos (by omega)]
  exact low_w_constant ⟨2 * j.val, by omega⟩

theorem low_odd_value (j : Fin 46) : wo j.val = 576 := by
  unfold wo zeroExtend
  rw [if_pos (by omega)]
  exact low_w_constant ⟨2 * j.val + 1, by omega⟩

theorem low_targets_lt_48 (j : Fin 46) {r : Nat} (hr : r ∈ indexTargets j.val) :
    r < 48 := by
  have h := low_targets_bound j
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h r hr)

theorem low_twice_targets_lt_48 (j : Fin 46)
    {r : Nat} (hr : r ∈ (indexTargets j.val).flatMap indexTargets) : r < 48 := by
  have h := low_twice_targets_bound j
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h r hr)

theorem low_even_gather (j : Fin 46) : sourceGather half we j.val = 576 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) we 576
  intro r hr
  exact low_even_value ⟨r, low_targets_lt_48 j hr |>.trans_le (by omega)⟩

theorem low_odd_gather (j : Fin 46) : sourceGather half wo j.val = 576 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) wo 576
  intro r hr
  exact low_odd_value ⟨r, low_targets_lt_48 j hr |>.trans_le (by omega)⟩

theorem low_even_double_gather (j : Fin 46) : sourceGather half (sourceGather half we) j.val = 576 := by
  apply source_gather_double_constant_on_targets half half_add_half j.val (by omega) we 576
  · intro r hr
    exact Nat.lt_of_lt_of_le (low_targets_lt_48 j hr) (by omega)
  · intro r hr
    exact low_even_value ⟨r, low_twice_targets_lt_48 j hr |>.trans_le (by omega)⟩

def pw : Nat → M := pointWeight half 7 5 (-5) point

theorem pw_low (n : Fin 92) : pw n.val = if n.val % 2 = 0 then 4032 else 6912 := by
  let j : Fin 46 := ⟨n.val / 2, by omega⟩
  by_cases hn : n.val % 2 = 0
  · have hnj : n.val = 2 * j.val := by dsimp [j]; omega
    rw [hnj]
    unfold pw pointWeight sourceChordTranspose
    unfold interleave chordDualEven
    simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
    rw [low_even_value j, low_even_gather j, low_odd_value j]
    decide
  · have hnj : n.val = 2 * j.val + 1 := by dsimp [j]; omega
    rw [hnj]
    unfold pw pointWeight sourceChordTranspose
    unfold interleave chordDualOdd
    simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
    rw [low_even_value j, low_even_gather j, low_even_double_gather j,
      low_odd_value j, low_odd_gather j]
    decide

theorem fixed_point1_low_sparse_zero (d : Fin 23) (s : Fin 3) :
    sparseObservation half (536870912 : M) 7 5 (-5) 5 0 7 z
      ⟨d.val, by omega⟩ s (.inr (.inl 1)) = 0 := by
  unfold sparseObservation
  change (pw (4 * d.val + s.val + 1) - 7 ^ (s.val + 1) * pw (4 * d.val)) -
      (pw (s.val + 1) - 7 ^ (s.val + 1) * pw 0) = 0
  have h1 : 4 * d.val + s.val + 1 < 92 := by omega
  have h2 : 4 * d.val < 92 := by omega
  have h3 : s.val + 1 < 92 := by omega
  rw [pw_low ⟨4 * d.val + s.val + 1, h1⟩,
    pw_low ⟨4 * d.val, h2⟩, pw_low ⟨s.val + 1, h3⟩, pw_low ⟨0, by omega⟩]
  fin_cases s <;> simp only [Nat.reduceMod, ↓reduceIte, Nat.reducePow]
  all_goals decide

#print axioms half_add_half
#print axioms low_even_gather
#print axioms low_odd_gather
#print axioms low_even_double_gather
#print axioms pw_low
#print axioms fixed_point1_low_sparse_zero

end
end AspisV8R19.R779FixedPoint1LowKernel
