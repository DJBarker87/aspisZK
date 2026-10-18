import RRDiagonalSubstitutionExpansionV27
import RRChildSliceTaylorV4
import RRChildSliceMultiplicityV3

open Polynomial
noncomputable section
namespace RRActualBivariateTaylorBridge
variable {K : Type*} [Field K]

def boundedInput (g : Nat → K[X]) (M i : Nat) : K[X] := if i ≤ M then g i else 0

def fixedParentSlice (g : Nat → K[X]) (a : K) (M : Nat) : Bivariate K :=
  ∑ i ∈ Finset.range (M + 1), C (X ^ i : K[X]) * substituteByChild (g i) a

def xCoeffSlice (q : Bivariate K) (n : Nat) : K[X] :=
  q.sum fun j c => C (c.coeff n) * X ^ j

theorem xCoeffSlice_coeff (q : Bivariate K) (n j : Nat) :
    (xCoeffSlice q n).coeff j = (q.coeff j).coeff n := by
  unfold xCoeffSlice
  rw [Polynomial.sum_def, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow]
    simp
  · intro b hb hbj
    have hjb : j ≠ b := fun h => hbj h.symm
    rw [Polynomial.coeff_C_mul_X_pow, if_neg hjb]
  · intro hj
    have hz : q.coeff j = 0 := Polynomial.notMem_support_iff.mp hj
    simp [hz]

private theorem parent_coeff_formula (g : Nat → K[X]) (a : K) (M n j : Nat) :
    (xCoeffSlice (fixedParentSlice g a M) n).coeff j =
      ∑ i ∈ Finset.range (M + 1),
        (if n = i + j then (Polynomial.taylor a (g i)).coeff j else 0) := by
  rw [xCoeffSlice_coeff]
  unfold fixedParentSlice
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, RRActualBivariateTaylorBridge.coeff_inner_substitution]
  have hprod (i : Nat) (c : K) :
      (X : K[X]) ^ i * (C c * X ^ j) = C c * X ^ (i + j) := by
    calc
      X ^ i * (C c * X ^ j) = (X ^ i * C c) * X ^ j := by rw [mul_assoc]
      _ = (C c * X ^ i) * X ^ j := by rw [mul_comm (X ^ i) (C c)]
      _ = C c * (X ^ i * X ^ j) := by rw [← mul_assoc]
      _ = C c * X ^ (i + j) := by rw [← pow_add]
  simp_rw [hprod, Polynomial.coeff_C_mul_X_pow]

theorem xCoeffSlice_fixedParent_formula
    (g : Nat → K[X]) (a : K) (M n j : Nat) :
    (xCoeffSlice (fixedParentSlice g a M) n).coeff j =
      (RRChildSliceTaylor.childCoeff (boundedInput g M) a n).coeff j := by
  rw [parent_coeff_formula]
  unfold RRChildSliceTaylor.childCoeff
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  classical
  let F : Nat → K := fun i => if n = i + j then (Polynomial.taylor a (g i)).coeff j else 0
  let G : Nat → K := fun i => if j = n - i then (Polynomial.taylor a (boundedInput g M i)).coeff (n - i) else 0
  change (∑ i ∈ Finset.range (M + 1), F i) = ∑ i ∈ Finset.range (n + 1), G i
  by_cases hnM : n ≤ M
  · have hcut : (∑ i ∈ Finset.range (M + 1), F i) =
        ∑ i ∈ Finset.range (n + 1), F i := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (by omega)
      · intro i hi hnot
        have hinM : i ≤ M := by
          have := Finset.mem_range.mp hi
          omega
        have hnot' : ¬ i < n + 1 := by
          simpa only [Finset.mem_range] using hnot
        have hgtN : n < i := by omega
        have : n ≠ i + j := by omega
        simp [F, this]
    rw [hcut]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    have hiM : i ≤ M := by omega
    by_cases heq : n = i + j
    · have hji : j = n - i := by omega
      dsimp only [F, G]
      rw [if_pos heq, if_pos hji]
      simp only [boundedInput, if_pos hiM]
      rw [← hji]
    · have hji : j ≠ n - i := by omega
      dsimp only [F, G]
      rw [if_neg heq, if_neg hji]
  · have hcut : (∑ i ∈ Finset.range (n + 1), G i) =
        ∑ i ∈ Finset.range (M + 1), G i := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (by omega)
      · intro i hi hnot
        have hinN : i ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        have hnot' : ¬ i < M + 1 := by
          simpa only [Finset.mem_range] using hnot
        have hgtM : M < i := by omega
        simp [G, boundedInput, Nat.not_le_of_gt hgtM]
    rw [hcut]
    apply Finset.sum_congr rfl
    intro i hi
    have hinM : i ≤ M := by
      have := Finset.mem_range.mp hi
      omega
    have hinN : i ≤ n := by omega
    by_cases heq : n = i + j
    · have hji : j = n - i := by omega
      dsimp only [F, G]
      rw [if_pos heq, if_pos hji]
      simp only [boundedInput, if_pos hinM]
      rw [← hji]
    · have hji : j ≠ n - i := by omega
      dsimp only [F, G]
      rw [if_neg heq, if_neg hji]

theorem xCoeffSlice_fixedParent_eq_childCoeff
    (g : Nat → K[X]) (a : K) (M n : Nat) :
    xCoeffSlice (fixedParentSlice g a M) n =
      RRChildSliceTaylor.childCoeff (boundedInput g M) a n := by
  ext j
  exact xCoeffSlice_fixedParent_formula g a M n j

def fixedParentCoeffSlice (g : Nat → K[X]) (a : K) (M n : Nat) : K[X] :=
  xCoeffSlice (fixedParentSlice g a M) n

theorem exists_actual_fixed_parent_first_nonzero_slice
    (g : Nat → K[X]) (a : K) (p : K[X]) (M : Nat)
    (hp : p ≠ 0) (hzero : g 0 = p) :
    ∃ v, v ≤ p.rootMultiplicity a ∧
      fixedParentCoeffSlice g a M v ≠ 0 ∧
      (∀ k < v, fixedParentCoeffSlice g a M k = 0) ∧
      (fixedParentCoeffSlice g a M v).natDegree ≤ p.rootMultiplicity a := by
  classical
  let g' : Nat → K[X] := boundedInput g M
  have hbase : g' 0 = p := by
    simp [g', boundedInput, hzero]
  have htop : RRChildSliceTaylor.childCoeff g' a (p.rootMultiplicity a) ≠ 0 := by
    have hc := RRChildSliceTaylor.childCoeff_top_coeff g' a (p.rootMultiplicity a)
    rw [hbase] at hc
    intro hz
    rw [hz] at hc
    exact (RRRootMultiplicityTaylor.taylor_coeff_ne_zero_at_rootMultiplicity p a hp) hc.symm
  have hex : ∃ n, RRChildSliceTaylor.childCoeff g' a n ≠ 0 :=
    ⟨p.rootMultiplicity a, htop⟩
  let v := Nat.find hex
  have hslice (n : Nat) : fixedParentCoeffSlice g a M n =
      RRChildSliceTaylor.childCoeff g' a n := by
    simpa [fixedParentCoeffSlice, g'] using xCoeffSlice_fixedParent_eq_childCoeff g a M n
  have hne : RRChildSliceTaylor.childCoeff g' a v ≠ 0 := Nat.find_spec hex
  have hv : v ≤ p.rootMultiplicity a := Nat.find_min' hex htop
  have hminimal : ∀ k < v, RRChildSliceTaylor.childCoeff g' a k = 0 := by
    intro k hkv
    by_contra hk
    have hle : v ≤ k := Nat.find_min' hex hk
    omega
  have hdegree : (RRChildSliceTaylor.childCoeff g' a v).natDegree ≤ p.rootMultiplicity a :=
    (RRChildSliceTaylor.childCoeff_natDegree_le g' a v).trans hv
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · rw [hslice]
    exact hne
  · intro k hkv
    rw [hslice]
    exact hminimal k hkv
  · rw [hslice]
    exact hdegree

#print axioms exists_actual_fixed_parent_first_nonzero_slice
end RRActualBivariateTaylorBridge
