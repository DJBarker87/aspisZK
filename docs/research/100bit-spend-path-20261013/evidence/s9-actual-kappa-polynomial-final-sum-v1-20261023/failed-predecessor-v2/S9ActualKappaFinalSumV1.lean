import S9ActualFinalSumV1
import S9ActualIndexedPowersSevenSemanticsV1
import S9ActualScalarFourTermMeaningV1
import S9ActualPairScalarQuarterFactsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualKappaFinalSumV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeWideDecodedArithmeticV1
open AspisR1S9ActualFinalSumV1
abbrev zero : W := aspis_core.field.wide_exact.WideExact.ZERO

theorem zero_canonical : Canonical zero :=
  AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical

theorem zero_decode : decode zero=0 := by
  have hz : AspisR1S9ActualPairScalarCallbackV1.toHelperW zero=
      AspisR1S9HelperP6.field.WideExact.ZERO := by
    simpa only [zero] using AspisR1S9ActualPairScalarQuarterFactsV1.mapped_zero_eq_helper
  have hm := AspisR1S9ActualScalarFourTermMeaningV1.mapped_native_decode zero
  rw [hz] at hm
  exact hm.symm.trans AspisR1S9TransparentFoldS2InstanceV1.zero_decode

def kappaTerm (parts : A) (kappa : W) (i : Nat) : AspisWideTower.WideExact :=
  if h : i<7 then decode kappa^i*decode (parts.val[i]'(by rw [parts.property];exact h))
  else 0

def kappaPolynomial (parts : A) (kappa : W) : AspisWideTower.WideExact :=
  ∑ i ∈ Finset.range 7, kappaTerm parts kappa i

/-- Existing indexed-power semantics instantiated at seven supplies BOTH the
canonical array and exact powers for the same native successful powers call. -/
theorem actual_powers_seven_good (kappa : W) (k : A) (hc : Canonical kappa)
    (hp : weights.powers 7#usize kappa=.ok k) : Good k := by
  intro i value hread
  exact (AspisR1S9ActualIndexedPowersSevenSemanticsV1.actual_powers_seven_success_decodes_powers
    kappa k hc hp i value hread).1

theorem actual_powers_partial_sum (parts k : A) (kappa : W) (hc : Canonical kappa)
    (hp : weights.powers 7#usize kappa=.ok k) :
    partialSum parts k 7=kappaPolynomial parts kappa := by
  unfold partialSum kappaPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  have hib : i<7 := Finset.mem_range.mp hi
  let j : Usize := Usize.ofNatCore i (by have hmax:=Usize.cMax_bound; scalar_tac)
  have hj : j.val=i := by simp only [j,Usize.ofNatCore_val_eq]
  have hjb : j.val<7 := by rw [hj];exact hib
  have hread := AspisR1S9FactorArrayEntryV1.index_atN k j hjb
  have hvalue := (AspisR1S9ActualIndexedPowersSevenSemanticsV1.actual_powers_seven_success_decodes_powers
    kappa k hc hp j _ hread).2
  unfold AspisR1S9FactorArrayEntryV1.atN at hvalue
  rw [←hj]
  simp only [term,kappaTerm,hjb,↓reduceDIte]
  rw [hvalue]

/-- The actual final two-fold shared or unshared loop computes the concrete
kappa polynomial of its own parts, with powers/zero guards discharged. Only
the parts' canonicality and kappa canonicality remain until whole-Pair assembly. -/
theorem actual_final_sum_is_kappa_polynomial (parts k : A) (kappa out : W)
    (hc : Canonical kappa) (hp : Good parts)
    (hk : weights.powers 7#usize kappa=.ok k)
    (hs : weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k zero=.ok out) :
    Canonical out ∧ decode out=kappaPolynomial parts kappa := by
  have hkg := actual_powers_seven_good kappa k hc hk
  have hzeroIndex : (0#usize : Usize).val=0 := rfl
  have hz : decode zero=partialSum parts k (0#usize).val := by
    simpa only [hzeroIndex,partialSum,Finset.range_zero,Finset.sum_empty] using zero_decode
  obtain ⟨hout,hmeaning⟩ := actual_final_sum_loop_success parts k
    {start:=0#usize,«end»:=7#usize} zero out hp hkg rfl (by decide) zero_canonical hz hs
  exact ⟨hout,hmeaning.trans (actual_powers_partial_sum parts k kappa hc hk)⟩

theorem actual_shared_final_sum_is_kappa_polynomial (parts k : A) (kappa out : W)
    (hc : Canonical kappa) (hp : Good parts)
    (hk : weights.powers 7#usize kappa=.ok k)
    (hs : weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} parts k zero=.ok out) :
    Canonical out ∧ decode out=kappaPolynomial parts kappa := by
  rw [shared_final_sum_eq] at hs
  exact actual_final_sum_is_kappa_polynomial parts k kappa out hc hp hk hs

#print axioms zero_canonical
#print axioms zero_decode
#print axioms actual_powers_seven_good
#print axioms actual_powers_partial_sum
#print axioms actual_final_sum_is_kappa_polynomial
#print axioms actual_shared_final_sum_is_kappa_polynomial
end AspisR1S9ActualKappaFinalSumV1
