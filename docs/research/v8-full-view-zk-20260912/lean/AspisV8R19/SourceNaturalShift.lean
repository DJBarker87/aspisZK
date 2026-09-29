import AspisV8R19.RetainedSparseShift
import AspisV8R17.ScatterDual

/-! Bind the current 512/513 source schedules to the retained generic
multiply-by-X proof. Only index schedules are checked concretely. -/
namespace AspisR19.SourceNaturalShift
open AspisV8R17 AspisCircleTensorBinding Polynomial RetainedSparseShift
noncomputable section

def countOnes : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, j => if j%2=0 then 0 else 1+countOnes fuel (j/2)

theorem countOnes_eq (fuel j : Nat) (hj : j<2^fuel) : countOnes fuel j=trailingOnes j := by
  induction fuel generalizing j with
  | zero =>
    have h : j=0 := by simpa using hj
    subst j
    simp [countOnes,trailingOnes]
  | succ fuel ih =>
    rw [countOnes,trailingOnes]
    split_ifs
    · rfl
    · rw [ih (j/2) (by rw [pow_succ] at hj; omega)]

def edgesWithCount (j count : Nat) : List (Nat × Nat) :=
  ((List.range count).map fun k => (j-(2^(k+1)-1),k+1)) ++ [(j+1,count)]
def carryEdges (j : Nat) : List (Nat × Nat) := edgesWithCount j (trailingOnes j)

theorem schedule_certificate : ∀ b : Fin 17, ∀ o : Fin 32,
    let j := 32*b.val+o.val
    j<513 → indexLoop 10 j 0=some (edgesWithCount j (countOnes 10 j)) := by decide

theorem schedule_formula (j : Nat) (hj : j<513) :
    indexLoop 10 j 0=some (carryEdges j) := by
  have h := schedule_certificate ⟨j/32,by omega⟩ ⟨j%32,by omega⟩
  have he : 32*(j/32)+j%32=j := by omega
  dsimp only at h
  rw [he] at h
  simpa only [countOnes_eq 10 j (by change j<1024; omega),carryEdges] using h hj

variable {K : Type*} [Field K] [NeZero (2 : K)]

theorem list_range_sum {A : Type*} [AddCommMonoid A] (f : Nat → A) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

theorem carry_polynomial (j : Nat) :
    ((carryEdges j).map fun e => C (((2:K)⁻¹)^e.2)*naturalLinePoly K e.1).sum =
      X*naturalLinePoly K j := by
  have h := (sparseFormula_eq_recursive (K:=K) j).trans (recursiveShiftPolynomial_eq_mul_X j)
  rw [sparseFormula_eq_carry_expansion] at h
  simp only [carryEdges,edgesWithCount,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,List.map_map,Function.comp_def,list_range_sum]
  simpa only [dyadic,inv_pow,add_comm] using h

theorem sourceGather_natural (x : K) (j : Nat) (hj : j<513) :
    sourceGather (2:K)⁻¹ (naturalLineValue x) j=x*naturalLineValue x j := by
  have hw := weightedIndexLoop_powers (2:K)⁻¹ 10 j 0
  simp only [pow_zero,schedule_formula j hj,Option.map_some] at hw
  unfold sourceGather
  rw [hw]
  simp only [Option.getD_some,List.map_map,Function.comp_def]
  have h := congrArg (Polynomial.eval x) (carry_polynomial (K:=K) j)
  simpa only [Polynomial.eval_listSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,List.map_map,Function.comp_def,naturalLineValue_eq_eval] using h

#print axioms countOnes_eq
#print axioms schedule_certificate
#print axioms schedule_formula
#print axioms list_range_sum
#print axioms carry_polynomial
#print axioms sourceGather_natural
end
end AspisR19.SourceNaturalShift
