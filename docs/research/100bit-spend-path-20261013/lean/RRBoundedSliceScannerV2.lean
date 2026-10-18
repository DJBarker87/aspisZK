import RRActualFixedParentConvolutionV7
import Mathlib.Algebra.Polynomial.Degree.Domain

open Polynomial
noncomputable section
namespace RRActualSliceScanner
variable {K : Type*} [Field K] [DecidableEq K]

def boundedSlicePredicate (g : Nat → K[X]) (a : K) (M n : Nat) : Bool :=
  decide (RRChildSliceTaylor.childCoeff
    (RRActualBivariateTaylorBridge.boundedInput g M) a n ≠ 0)

def boundedFirstSliceSearch
    (g : Nat → K[X]) (a : K) (p : K[X]) (M : Nat) : Option Nat :=
  (List.range (p.natDegree + 1)).find? (boundedSlicePredicate g a M)

theorem rootMultiplicity_le_natDegree (p : K[X]) (a : K) (hp : p ≠ 0) :
    p.rootMultiplicity a ≤ p.natDegree := by
  have hdiv : (X - C a) ^ p.rootMultiplicity a ∣ p :=
    p.pow_rootMultiplicity_dvd a
  have hdeg := natDegree_le_of_dvd hdiv hp
  have hpow : ((X - C a) ^ p.rootMultiplicity a).natDegree = p.rootMultiplicity a := by
    simp
  simpa [hpow] using hdeg

theorem boundedFirstSliceSearch_complete
    (g : Nat → K[X]) (a : K) (p : K[X]) (M : Nat)
    (hp : p ≠ 0) (hzero : g 0 = p) :
    ∃ v, boundedFirstSliceSearch g a p M = some v ∧
      v ≤ p.rootMultiplicity a ∧
      RRActualBivariateTaylorBridge.fixedParentCoeffSlice g a M v ≠ 0 ∧
      (∀ k < v,
        RRActualBivariateTaylorBridge.fixedParentCoeffSlice g a M k = 0) ∧
      (RRActualBivariateTaylorBridge.fixedParentCoeffSlice g a M v).natDegree ≤
        p.rootMultiplicity a := by
  classical
  let g' : Nat → K[X] := RRActualBivariateTaylorBridge.boundedInput g M
  have hbase : g' 0 = p := by simp [g', RRActualBivariateTaylorBridge.boundedInput, hzero]
  let r := p.rootMultiplicity a
  have hrdeg : r ≤ p.natDegree := rootMultiplicity_le_natDegree p a hp
  have htop : RRChildSliceTaylor.childCoeff g' a r ≠ 0 := by
    have hc := RRChildSliceTaylor.childCoeff_top_coeff g' a r
    rw [hbase] at hc
    intro hz
    rw [hz] at hc
    exact (RRRootMultiplicityTaylor.taylor_coeff_ne_zero_at_rootMultiplicity p a hp) hc.symm
  have hpred : boundedSlicePredicate g a M r = true := by
    simp [boundedSlicePredicate, g', htop]
  have hmem : r ∈ List.range (p.natDegree + 1) := by
    simp only [List.mem_range]
    omega
  have hsome : (List.range (p.natDegree + 1)).find?
      (boundedSlicePredicate g a M) |>.isSome := by
    rw [List.find?_isSome]
    exact ⟨r, hmem, hpred⟩
  obtain ⟨v, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have hfindSpec := (List.find?_eq_some_iff_getElem.mp hfind)
  obtain ⟨hvPred, i, hi, hget, hprior⟩ := hfindSpec
  have hget' : i = v := by simpa using hget
  have hvle : v ≤ r := by
    by_contra hnot
    have hri : r < i := by omega
    have hnotPred := hprior r hri
    have hrval : (List.range (p.natDegree + 1))[r] = r := by simp
    rw [hrval, hpred] at hnotPred
    contradiction
  have hslice (n : Nat) :
      RRActualBivariateTaylorBridge.fixedParentCoeffSlice g a M n =
        RRChildSliceTaylor.childCoeff g' a n := by
    simpa [g', RRActualBivariateTaylorBridge.fixedParentCoeffSlice] using
      RRActualBivariateTaylorBridge.xCoeffSlice_fixedParent_eq_childCoeff g a M n
  have hnonzero :
      RRActualBivariateTaylorBridge.fixedParentCoeffSlice g a M v ≠ 0 := by
    rw [hslice]
    simpa [boundedSlicePredicate, g'] using hvPred
  have hminimal : ∀ k < v,
      RRActualBivariateTaylorBridge.fixedParentCoeffSlice g a M k = 0 := by
    intro k hkv
    have hnotPred := hprior k (by omega)
    have hkval : (List.range (p.natDegree + 1))[k] = k := by simp
    rw [hkval] at hnotPred
    have hkzero : RRChildSliceTaylor.childCoeff g' a k = 0 := by
      by_contra hk
      have : boundedSlicePredicate g a M k = true := by
        simp [boundedSlicePredicate, g', hk]
      simp [this] at hnotPred
    rw [hslice]
    exact hkzero
  have hdegree :
      (RRActualBivariateTaylorBridge.fixedParentCoeffSlice g a M v).natDegree ≤ r := by
    rw [hslice]
    exact (RRChildSliceTaylor.childCoeff_natDegree_le g' a v).trans hvle
  refine ⟨v, hfind, hvle, hnonzero, hminimal, ?_⟩
  simpa [r] using hdegree

#print axioms boundedFirstSliceSearch_complete
end RRActualSliceScanner
