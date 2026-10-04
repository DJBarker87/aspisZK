import AspisV8R19.R779FixedPoint1LowKernel
import AspisV8R19.R771Point02Transport
namespace AspisV8R19.R783FixedOrdinaryLowKernel
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R777GatherConstantOnTargets
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R776LowPoint1Transport
open AspisV8R19.R748JointWitnessPointEntry hiding w
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
abbrev M := R748JointWitnessPointEntry.M
abbrev half : M := R779FixedPoint1LowKernel.half
 theorem half_add_half : half + half = 1 := R779FixedPoint1LowKernel.half_add_half
 theorem z_eq : z = R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> simp [z, R750WitnessPointSupport.zFin10]
def w : Nat → M := extendFin1024 (transportDual inactive 1023 order
  (rawOrdinaryOriginal z 5))
theorem low_w_constant (j : Fin 96) : w j.val = 14400 := by
  have hg := low_guard j
  have h0 : sourcePointBasis (SourceStatementPoints.points z 0)
      (order (lowIndex j)).val = 0 := by
    rw [z_eq]
    exact R750WitnessPointSupport.source_basis_zero_of_bits _
      (hg.elim Or.inl (fun h => Or.inr (Or.inl h)))
  have h1 : sourcePointBasis (SourceStatementPoints.points z 1)
      (order (lowIndex j)).val = 0 :=
    R752SharedWitnessPointSupport.point1_source_basis_zero _ hg
  have h2 : sourcePointBasis (SourceStatementPoints.points z 2)
      (order (lowIndex j)).val = 0 := by
    rw [z_eq]
    exact R752SharedWitnessPointSupport.point2_source_basis_zero _
      (hg.elim Or.inl (fun h => Or.inr (Or.inl h)))
  have p0 : sourcePointBasis (SourceStatementPoints.points z 0) 1023 = 0 := by
    rw [z_eq]
    exact R771Point02Transport.point0_pivot_basis_zero
  have p1 : sourcePointBasis (SourceStatementPoints.points z 1) 1023 = -576 :=
    R754Point1GuardedTransport.point1_pivot_basis_neg
  have p2 : sourcePointBasis (SourceStatementPoints.points z 2) 1023 = 0 := by
    rw [z_eq]
    exact R771Point02Transport.point2_pivot_basis_zero
  have hm : order (lowIndex j) ∈ inactive :=
    (Finset.mem_erase.mp (low_member j)).2
  have hp : (1023 : Fin 1024) ∈ inactive := by decide
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (rawOrdinaryOriginal z 5) (lowIndex j) = 14400
  rw [transportDual, if_pos (low_member j)]
  simp only [rawOrdinaryOriginal, sourceOriginalWeight_eq, Bool.false_eq_true,
    if_false, h0, h1, h2, p0, p1, p2, hm, hp, if_true]
  decide
abbrev we : Nat → M := zeroExtend 512 (fun i => w (2*i))
abbrev wo : Nat → M := zeroExtend 512 (fun i => w (2*i+1))
theorem low_even_value (j : Fin 46) : we j.val = 14400 := by
  unfold we zeroExtend
  rw [if_pos (by omega)]
  exact low_w_constant ⟨2 * j.val, by omega⟩

theorem low_odd_value (j : Fin 46) : wo j.val = 14400 := by
  unfold wo zeroExtend
  rw [if_pos (by omega)]
  exact low_w_constant ⟨2 * j.val + 1, by omega⟩

theorem low_even_input (r : Nat) (hr : r < 48) : we r = 14400 := by
  unfold we zeroExtend
  rw [if_pos (by omega)]
  exact low_w_constant ⟨2 * r, by omega⟩

theorem low_odd_input (r : Nat) (hr : r < 48) : wo r = 14400 := by
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

theorem low_even_gather (j : Fin 46) : sourceGather half we j.val = 14400 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) we 14400
  intro r hr
  exact low_even_input r (low_targets_lt_48 j hr)

theorem low_odd_gather (j : Fin 46) : sourceGather half wo j.val = 14400 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) wo 14400
  intro r hr
  exact low_odd_input r (low_targets_lt_48 j hr)

theorem low_even_double_gather (j : Fin 46) : sourceGather half (sourceGather half we) j.val = 14400 := by
  apply source_gather_double_constant_on_targets half half_add_half j.val (by omega) we 14400
  · intro r hr
    exact Nat.lt_of_lt_of_le (low_targets_lt_48 j hr) (by omega)
  · intro r hr
    exact low_even_input r (low_twice_targets_lt_48 j hr)

def pw : Nat → M := sourceChordTranspose half w 7 5 (-5)

theorem pw_low (n : Fin 92) : pw n.val = if n.val % 2 = 0 then 100800 else 172800 := by
  let j : Fin 46 := ⟨n.val / 2, by omega⟩
  by_cases hn : n.val % 2 = 0
  · have hnj : n.val = 2 * j.val := by dsimp [j]; omega
    rw [hnj]
    have hmod : (2 * j.val) % 2 = 0 := by omega
    have hdiv : (2 * j.val) / 2 = j.val := by omega
    unfold pw sourceChordTranspose
    unfold interleave
    simp only [hmod, if_pos, hdiv]
    unfold chordDualEven
    change 7 * we j.val + 5 * sourceGather half we j.val + (-5) * wo j.val = 100800
    rw [low_even_value j, low_even_gather j, low_odd_value j]
    decide
  · have hnj : n.val = 2 * j.val + 1 := by dsimp [j]; omega
    rw [hnj]
    have hmod : (2 * j.val + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
    unfold pw sourceChordTranspose
    unfold interleave
    simp only [hmod, if_false, hdiv]
    unfold chordDualOdd
    change -5 * (we j.val - sourceGather half (sourceGather half we) j.val) +
      7 * wo j.val + 5 * sourceGather half wo j.val = 172800
    rw [low_even_value j, low_even_double_gather j,
      low_odd_value j, low_odd_gather j]
    decide


theorem ordinary_low (n : Fin 92) :
    rawOrdinaryWeight half 7 5 (-5) 5 0 z n.val =
      if n.val % 2 = 0 then 100800 else 172800 := by
  unfold rawOrdinaryWeight sourceQuotientWeights
  rw [sourceImageUpdates_apply]
  have h1 : n.val ≠ 1023 := by omega
  have h2 : n.val ≠ 1022 := by omega
  have h3 : n.val ≠ 1021 := by omega
  simp only [Bool.false_eq_true, if_false, h1, h2, h3, add_zero, sub_zero]
  exact pw_low n
 theorem ordinary_low_period (d : Fin 23) (t : Fin 4) :
    rawOrdinaryWeight half 7 5 (-5) 5 0 z (4*d.val+t.val) =
      rawOrdinaryWeight half 7 5 (-5) 5 0 z t.val := by
  rw [ordinary_low ⟨4*d.val+t.val, by omega⟩,
    ordinary_low ⟨t.val, by omega⟩]
  have hm : (4*d.val+t.val) % 2 = t.val % 2 := by omega
  rw [hm]
 theorem coefficient_low_zero (d : Fin 23) (s : Fin 3) (k : Fin 5) :
    sparseObservation half (536870912 : M) 7 5 (-5) 5 0 7 z
      ⟨d.val, by omega⟩ s (.inr (.inr k)) = 0 := by
  have hr (slot : Fin 4) :
      rowWeight 256 (relationIndex k) (536870912 : M)
        (fun i => rawOrdinaryWeight half 7 5 (-5) 5 0 z (4*i.1.val+i.2.val))
        (cast255 ⟨d.val, by omega⟩) slot =
      rowWeight 256 (relationIndex k) (536870912 : M)
        (fun i => rawOrdinaryWeight half 7 5 (-5) 5 0 z (4*i.1.val+i.2.val))
        0 slot := by
    unfold rowWeight
    apply Finset.sum_congr rfl
    intro t _
    change _ * rawOrdinaryWeight half 7 5 (-5) 5 0 z (4*d.val+t.val) =
      _ * rawOrdinaryWeight half 7 5 (-5) 5 0 z (4*0+t.val)
    rw [ordinary_low_period, Nat.mul_zero, Nat.zero_add]
  simp only [sparseObservation]
  rw [hr, hr]
  exact sub_self _
#print axioms low_w_constant
#print axioms low_even_gather
#print axioms low_odd_gather
#print axioms low_even_double_gather
#print axioms ordinary_low
#print axioms ordinary_low_period
#print axioms coefficient_low_zero
end
end AspisV8R19.R783FixedOrdinaryLowKernel
