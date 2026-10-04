import AspisV8R19.R779FixedPoint1LowKernel
import AspisV8R19.R771Point02Transport
import AspisV8R19.R776LowPoint1Transport

/-! Fixed-witness low gather kernel for statement points zero and two. -/
set_option autoImplicit false
namespace AspisV8R19.R782Point02LowKernel

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.R752SharedWitnessPointSupport
open AspisV8R19.R771Point02Transport
open AspisV8R19.R776LowPoint1Transport
open AspisV8R19.R779FixedPoint1LowKernel
open AspisV8R19.R777GatherConstantOnTargets
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R748JointWitnessPointEntry
noncomputable section

abbrev M := R748JointWitnessPointEntry.M

lemma z_eq_zfin : z = zFin10 (F := M) := by
  funext i
  fin_cases i <;> norm_num [z, zFin10]

lemma point0_eq : SourceStatementPoints.points z 0 = point0 (F := M) := by
  rw [z_eq_zfin]
  rfl

lemma point2_eq : SourceStatementPoints.points z 2 = point2 (F := M) := by
  rw [z_eq_zfin]
  rfl

def w0 (i : Nat) : M := extendFin1024 (transportDual inactive 1023 order
    (fun j => sourcePointBasis (point0 (F := M)) j.val)) i
def w2 (i : Nat) : M := extendFin1024 (transportDual inactive 1023 order
    (fun j => sourcePointBasis (point2 (F := M)) j.val)) i

theorem w0_low (j : Fin 96) : w0 j.val = 0 := by
  unfold w0 extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order
    (fun k : Fin 1024 => sourcePointBasis (point0 (F := M)) k.val) j = 0
  rw [point0_transport_exact]
  exact source_basis_zero_of_bits (F := M) (order j).val (low_guard j)

theorem w2_low (j : Fin 96) : w2 j.val = 0 := by
  unfold w2 extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order
    (fun k : Fin 1024 => sourcePointBasis (point2 (F := M)) k.val) j = 0
  rw [point2_transport_exact]
  exact point2_source_basis_zero (F := M) (order j).val (Or.inl (low_guard j))

abbrev we0 : Nat → M := zeroExtend 512 (fun i => w0 (2 * i))
abbrev wo0 : Nat → M := zeroExtend 512 (fun i => w0 (2 * i + 1))
abbrev we2 : Nat → M := zeroExtend 512 (fun i => w2 (2 * i))
abbrev wo2 : Nat → M := zeroExtend 512 (fun i => w2 (2 * i + 1))

theorem low_input0_even (r : Nat) (hr : r < 48) : we0 r = 0 := by
  unfold we0 zeroExtend
  rw [if_pos (by omega)]
  exact w0_low ⟨2 * r, by omega⟩
theorem low_input0_odd (r : Nat) (hr : r < 48) : wo0 r = 0 := by
  unfold wo0 zeroExtend
  rw [if_pos (by omega)]
  exact w0_low ⟨2 * r + 1, by omega⟩
theorem low_input2_even (r : Nat) (hr : r < 48) : we2 r = 0 := by
  unfold we2 zeroExtend
  rw [if_pos (by omega)]
  exact w2_low ⟨2 * r, by omega⟩
theorem low_input2_odd (r : Nat) (hr : r < 48) : wo2 r = 0 := by
  unfold wo2 zeroExtend
  rw [if_pos (by omega)]
  exact w2_low ⟨2 * r + 1, by omega⟩

theorem targets_lt48 (j : Fin 46) {r : Nat} (hr : r ∈ indexTargets j.val) : r < 48 := by
  have h := low_targets_bound j
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h r hr)
theorem twice_targets_lt48 (j : Fin 46)
    {r : Nat} (hr : r ∈ (indexTargets j.val).flatMap indexTargets) : r < 48 := by
  have h := low_twice_targets_bound j
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h r hr)

theorem gather0e (j : Fin 46) : sourceGather half we0 j.val = 0 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) we0 0
  intro r hr; exact low_input0_even r (targets_lt48 j hr)
theorem gather0o (j : Fin 46) : sourceGather half wo0 j.val = 0 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) wo0 0
  intro r hr; exact low_input0_odd r (targets_lt48 j hr)
theorem gather0ee (j : Fin 46) : sourceGather half (sourceGather half we0) j.val = 0 := by
  apply source_gather_double_constant_on_targets half half_add_half j.val (by omega) we0 0
  · intro r hr; omega
  · intro r hr; exact low_input0_even r (twice_targets_lt48 j hr)
theorem gather2e (j : Fin 46) : sourceGather half we2 j.val = 0 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) we2 0
  intro r hr; exact low_input2_even r (targets_lt48 j hr)
theorem gather2o (j : Fin 46) : sourceGather half wo2 j.val = 0 := by
  apply source_gather_constant_on_targets half half_add_half j.val (by omega) wo2 0
  intro r hr; exact low_input2_odd r (targets_lt48 j hr)
theorem gather2ee (j : Fin 46) : sourceGather half (sourceGather half we2) j.val = 0 := by
  apply source_gather_double_constant_on_targets half half_add_half j.val (by omega) we2 0
  · intro r hr; omega
  · intro r hr; exact low_input2_even r (twice_targets_lt48 j hr)

def pw0 : Nat → M := pointWeight half 7 5 (-5) (point0 (F := M))
def pw2 : Nat → M := pointWeight half 7 5 (-5) (point2 (F := M))

theorem pw0_low (n : Fin 92) : pw0 n.val = 0 := by
  let j : Fin 46 := ⟨n.val / 2, by omega⟩
  by_cases hn : n.val % 2 = 0
  · have hnj : n.val = 2 * j.val := by dsimp [j]; omega
    rw [hnj]
    have hmod : (2 * j.val) % 2 = 0 := by omega
    have hdiv : (2 * j.val) / 2 = j.val := by omega
    unfold pw0 pointWeight sourceChordTranspose interleave
    simp only [hmod, if_pos, hdiv]
    unfold chordDualEven
    change 7 * we0 j.val + 5 * sourceGather half we0 j.val + (-5) * wo0 j.val = 0
    rw [low_input0_even j.val (by omega), gather0e j, low_input0_odd j.val (by omega)]
    ring
  · have hnj : n.val = 2 * j.val + 1 := by dsimp [j]; omega
    rw [hnj]
    have hmod : (2 * j.val + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
    unfold pw0 pointWeight sourceChordTranspose interleave
    simp only [hmod, if_false, hdiv]
    unfold chordDualOdd
    change -5 * (we0 j.val - sourceGather half (sourceGather half we0) j.val) +
      7 * wo0 j.val + 5 * sourceGather half wo0 j.val = 0
    rw [low_input0_even j.val (by omega), gather0ee j,
      low_input0_odd j.val (by omega), gather0o j]
    ring

theorem pw2_low (n : Fin 92) : pw2 n.val = 0 := by
  let j : Fin 46 := ⟨n.val / 2, by omega⟩
  by_cases hn : n.val % 2 = 0
  · have hnj : n.val = 2 * j.val := by dsimp [j]; omega
    rw [hnj]
    have hmod : (2 * j.val) % 2 = 0 := by omega
    have hdiv : (2 * j.val) / 2 = j.val := by omega
    unfold pw2 pointWeight sourceChordTranspose interleave
    simp only [hmod, if_pos, hdiv]
    unfold chordDualEven
    change 7 * we2 j.val + 5 * sourceGather half we2 j.val + (-5) * wo2 j.val = 0
    rw [low_input2_even j.val (by omega), gather2e j, low_input2_odd j.val (by omega)]
    ring
  · have hnj : n.val = 2 * j.val + 1 := by dsimp [j]; omega
    rw [hnj]
    have hmod : (2 * j.val + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
    unfold pw2 pointWeight sourceChordTranspose interleave
    simp only [hmod, if_false, hdiv]
    unfold chordDualOdd
    change -5 * (we2 j.val - sourceGather half (sourceGather half we2) j.val) +
      7 * wo2 j.val + 5 * sourceGather half wo2 j.val = 0
    rw [low_input2_even j.val (by omega), gather2ee j,
      low_input2_odd j.val (by omega), gather2o j]
    ring

theorem fixed_point0_low_sparse_zero (d : Fin 23) (s : Fin 3) :
    sparseObservation half (536870912 : M) 7 5 (-5) 5 0 7 z
      ⟨d.val, by omega⟩ s (.inr (.inl 0)) = 0 := by
  unfold sparseObservation
  rw [point0_eq]
  change (pw0 (4*d.val+s.val+1) - 7^(s.val+1)*pw0 (4*d.val)) -
    (pw0 (s.val+1) - 7^(s.val+1)*pw0 0) = 0
  rw [pw0_low ⟨4*d.val+s.val+1,by omega⟩,pw0_low ⟨4*d.val,by omega⟩,
    pw0_low ⟨s.val+1,by omega⟩,pw0_low ⟨0,by omega⟩]
  ring

theorem fixed_point2_low_sparse_zero (d : Fin 23) (s : Fin 3) :
    sparseObservation half (536870912 : M) 7 5 (-5) 5 0 7 z
      ⟨d.val, by omega⟩ s (.inr (.inl 2)) = 0 := by
  unfold sparseObservation
  rw [point2_eq]
  change (pw2 (4*d.val+s.val+1) - 7^(s.val+1)*pw2 (4*d.val)) -
    (pw2 (s.val+1) - 7^(s.val+1)*pw2 0) = 0
  rw [pw2_low ⟨4*d.val+s.val+1,by omega⟩,pw2_low ⟨4*d.val,by omega⟩,
    pw2_low ⟨s.val+1,by omega⟩,pw2_low ⟨0,by omega⟩]
  ring

#print axioms w0_low
#print axioms w2_low
#print axioms gather0e
#print axioms gather0ee
#print axioms gather2e
#print axioms gather2ee
#print axioms pw0_low
#print axioms pw2_low
#print axioms fixed_point0_low_sparse_zero
#print axioms fixed_point2_low_sparse_zero

end
end AspisV8R19.R782Point02LowKernel
