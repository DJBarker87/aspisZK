import RRScannedNormalizedTransition

namespace RRPrefixCollector

/-- Executable prefix enumeration. Field polynomials occur only in the
correctness interpretation below, never in this program's data or tests. -/
def collect {K S : Type*} (zeroTest : S → Bool) (children : S → List (K × S)) :
    Nat → S → List (List K)
  | 0, s => if zeroTest s then [[]] else []
  | d+1, s => (children s).flatMap fun (a,t) => (collect zeroTest children d t).map (a :: ·)

open Polynomial
noncomputable section
variable {K S : Type*} [Field K]
open RRDenseCoeffVector RRRootDescent

theorem toPolynomial_nil : toPolynomial ([] : List K) = 0 := by
  simp [toPolynomial]

theorem toPolynomial_cons (a : K) (cs : List K) :
    toPolynomial (a :: cs) = C a + X * toPolynomial cs := by
  ext n
  cases n with
  | zero => simp [coeff_toPolynomial, coeffAt]
  | succ n => simp [coeff_toPolynomial, coeffAt, Polynomial.coeff_X_mul]

theorem tail_degree_bound (d : Nat) (f : K[X])
    (hbound : f = 0 ∨ f.natDegree < d+1) :
    f.divX = 0 ∨ f.divX.natDegree < d := by
  by_cases hdegree : f.natDegree = 0
  · left
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree, Polynomial.divX_C]
  · right
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    rcases hbound with hz | hlt
    · subst f
      simp at hdegree
    · omega

/-- Completeness of the actual recursive prefix program from the local
descent interface. Root finding/state normalization must instantiate that
interface; it is not silently assumed to be an efficient decoder. -/
theorem collect_complete
    (zeroTest : S → Bool) (children : S → List (K × S))
    (model : S → (K[X])[X])
    (hzero : ∀ s, zeroTest s = true ↔ (model s).eval 0 = 0)
    (hstep : ∀ s f, (model s).eval f = 0 →
      ∃ a t, (a,t) ∈ children s ∧ a = f.coeff 0 ∧ (model t).eval f.divX = 0)
    (d : Nat) (s : S) (f : K[X])
    (hroot : (model s).eval f = 0)
    (hbound : f = 0 ∨ f.natDegree < d) :
    ∃ cs ∈ collect zeroTest children d s, toPolynomial cs = f := by
  induction d generalizing s f with
  | zero =>
    have hf : f = 0 := hbound.resolve_right (Nat.not_lt_zero _)
    subst f
    refine ⟨[], ?_, toPolynomial_nil⟩
    simp [collect, (hzero s).mpr hroot]
  | succ d ih =>
    obtain ⟨a,t,hmem,ha,hrootTail⟩ := hstep s f hroot
    obtain ⟨cs,hcs,hread⟩ := ih t f.divX hrootTail (tail_degree_bound d f hbound)
    refine ⟨a :: cs, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨(a,t),hmem,List.mem_map.mpr ⟨cs,hcs,rfl⟩⟩
    · rw [toPolynomial_cons, hread, ha, head_tail]

/-- Every emitted candidate is a root when the concrete transition is
root preserving and the final zero test is exact. -/
theorem collect_sound
    (zeroTest : S → Bool) (children : S → List (K × S))
    (model : S → (K[X])[X])
    (hzero : ∀ s, zeroTest s = true ↔ (model s).eval 0 = 0)
    (hstep : ∀ s a t, (a,t) ∈ children s → ∀ f,
      (model t).eval f = 0 → (model s).eval (C a + X * f) = 0)
    (d : Nat) (s : S) (cs : List K)
    (hmem : cs ∈ collect zeroTest children d s) :
    (model s).eval (toPolynomial cs) = 0 := by
  induction d generalizing s cs with
  | zero =>
    by_cases hz : zeroTest s = true
    · simp [collect, hz] at hmem
      subst cs
      rw [toPolynomial_nil]
      exact (hzero s).mp hz
    · simp [collect, hz] at hmem
  | succ d ih =>
    obtain ⟨⟨a,t⟩,hchild,hmap⟩ := List.mem_flatMap.mp hmem
    obtain ⟨tail,htail,hcs⟩ := List.mem_map.mp hmap
    subst cs
    rw [toPolynomial_cons]
    exact hstep s a t hchild (toPolynomial tail) (ih t tail htail)

#print axioms collect
#print axioms collect_complete
#print axioms collect_sound
end
end RRPrefixCollector
