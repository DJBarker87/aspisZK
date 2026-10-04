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

theorem low_even_input (r : Nat) (hr : r < 48) : we r = 576 := by
  unfold we zeroExtend
  rw [if_pos (by omega)]
  exact low_w_constant ⟨2 * r, by omega⟩

theorem low_odd_input (r : Nat) (hr : r < 48) : wo r = 576 := by
  unfold wo zeroExtend
  rw [if_pos (by omega)]
  exact low_w_constant ⟨2 * r + 1, by omega⟩

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
  exact low_even_input r (low_targets_lt_48 j hr)

theorem low_odd_gather (j : Fin 46) : sourceGather half wo j.val = 576 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) wo 576
  intro r hr
  exact low_odd_input r (low_targets_lt_48 j hr)

theorem low_even_double_gather (j : Fin 46) : sourceGather half (sourceGather half we) j.val = 576 := by
  apply source_gather_double_constant_on_targets half half_add_half j.val (by omega) we 576
  · intro r hr
    exact Nat.lt_of_lt_of_le (low_targets_lt_48 j hr) (by omega)
  · intro r hr
    exact low_even_input r (low_twice_targets_lt_48 j hr)

def pw : Nat → M := pointWeight half 7 5 (-5) point

theorem pw_low (n : Fin 92) : pw n.val = if n.val % 2 = 0 then 4032 else 6912 := by
  let j : Fin 46 := ⟨n.val / 2, by omega⟩
  by_cases hn : n.val % 2 = 0
  · have hnj : n.val = 2 * j.val := by dsimp [j]; omega
    rw [hnj]
    have hmod : (2 * j.val) % 2 = 0 := by omega
    have hdiv : (2 * j.val) / 2 = j.val := by omega
    unfold pw pointWeight sourceChordTranspose
    unfold interleave
    simp only [hmod, if_pos, hdiv]
    unfold chordDualEven
    change 7 * we j.val + 5 * sourceGather half we j.val - 5 * wo j.val = 4032
    rw [low_even_value j, low_even_gather j, low_odd_value j]
    decide
  · have hnj : n.val = 2 * j.val + 1 := by dsimp [j]; omega
    rw [hnj]
    have hmod : (2 * j.val + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
    unfold pw pointWeight sourceChordTranspose
    unfold interleave
    simp only [hmod, if_false, hdiv]
    unfold chordDualOdd
    change -5 * (we j.val - sourceGather half (sourceGather half we) j.val) +
      7 * wo j.val + 5 * sourceGather half wo j.val = 6912
    rw [low_even_value j, low_even_gather j, low_even_double_gather j,
      low_odd_value j, low_odd_gather j]
    decide

theorem pw_low_even (n : Nat) (hn : n < 92) (he : n % 2 = 0) : pw n = 4032 := by
  simpa [he] using pw_low ⟨n, hn⟩

theorem pw_low_odd (n : Nat) (hn : n < 92) (ho : n % 2 ≠ 0) : pw n = 6912 := by
  simpa [ho] using pw_low ⟨n, hn⟩

theorem fixed_point1_low_sparse_zero (d : Fin 23) (s : Fin 3) :
    sparseObservation half (536870912 : M) 7 5 (-5) 5 0 7 z
      ⟨d.val, by omega⟩ s (.inr (.inl 1)) = 0 := by
  unfold sparseObservation
  change (pw (4 * d.val + s.val + 1) - 7 ^ (s.val + 1) * pw (4 * d.val)) -
      (pw (s.val + 1) - 7 ^ (s.val + 1) * pw 0) = 0
  have h1 : 4 * d.val + s.val + 1 < 92 := by omega
  have h2 : 4 * d.val < 92 := by omega
  have h3 : s.val + 1 < 92 := by omega
  have hbase : pw (4 * d.val) = 4032 :=
    pw_low_even _ h2 (by omega)
  have hp0 : pw 0 = 4032 := pw_low_even _ (by omega) (by decide)
  fin_cases s
  · have hnext : pw (4 * d.val + 1) = 6912 :=
      pw_low_odd _ h1 (by omega)
    have hone : pw 1 = 6912 := pw_low_odd _ (by omega) (by decide)
    rw [hnext, hbase, hone, hp0]
    decide
  · have hnext : pw (4 * d.val + 2) = 4032 :=
      pw_low_even _ h1 (by omega)
    have htwo : pw 2 = 4032 := pw_low_even _ (by omega) (by decide)
    rw [hnext, hbase, htwo, hp0]
    decide
  · have hnext : pw (4 * d.val + 3) = 6912 :=
      pw_low_odd _ h1 (by omega)
    have hthree : pw 3 = 6912 := pw_low_odd _ (by omega) (by decide)
    rw [hnext, hbase, hthree, hp0]
    decide

#print axioms half_add_half
#print axioms low_even_gather
#print axioms low_odd_gather
#print axioms low_even_double_gather
#print axioms pw_low
#print axioms fixed_point1_low_sparse_zero

end
end AspisV8R19.R779FixedPoint1LowKernel
