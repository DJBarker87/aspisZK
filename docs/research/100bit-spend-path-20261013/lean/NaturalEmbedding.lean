import R1ConcreteProjection

/-! Prime-field-compatible embedding identities for the natural line basis.
These are algebraic plumbing lemmas only; no source, runtime, or protocol
claim is made. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.NaturalEmbedding

open AspisCircleGroupOrder
open AspisCircleTensorBinding
open AspisV5FriReleasedLineGeometry

variable {K E : Type} [Field K] [Field E]

theorem map_doubledFactor (iota : K →+* E) (x : K) (n : Nat) :
    iota (doubledFactor x n) = doubledFactor (iota x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [doubledFactor, map_sub, map_mul, map_pow, map_ofNat,
        map_one, ih]

theorem map_naturalLineValue (iota : K →+* E) (x : K) (n : Nat) :
    iota (naturalLineValue x n) = naturalLineValue (iota x) n := by
  simp only [naturalLineValue, map_prod, map_doubledFactor]

variable [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) K] [Algebra (ZMod P) E]

/-- A ring hom from the prime field agrees with the canonical algebra map. -/
theorem map_algebraMap_prime (iota : K →+* E) (z : ZMod P) :
    iota (algebraMap (ZMod P) K z) = algebraMap (ZMod P) E z := by
  have unique : iota.comp (algebraMap (ZMod P) K) =
      algebraMap (ZMod P) E := Subsingleton.elim _ _
  exact DFunLike.congr_fun unique z

/-- Evaluate the concrete log-16 encoder at the parent of any queried
log-18 position as a sum of the embedded K-valued natural basis. -/
theorem secondEncoder_query_eq_natural_sum {n : Nat}
    (iota : K →+* E) (f : Fin 64 → E)
    (q : Fin n → Fin 262144) (i : Fin n) :
    AspisR1.ConcreteProjection.secondEncoder f
        (AspisR1.parentIndex (n := 65536) (q i)) =
      ∑ j : Fin 64,
        f j * iota (naturalLineValue
          (algebraMap (ZMod P) K
            (storedLine16X (AspisR1.parentIndex (n := 65536) (q i)))) j.val) := by
  let parent := AspisR1.parentIndex (n := 65536) (q i)
  have hpoint :
      algebraMap (ZMod P) E (storedLine16X parent) =
        iota (algebraMap (ZMod P) K (storedLine16X parent)) :=
    (map_algebraMap_prime (K := K) (E := E) iota
      (storedLine16X parent)).symm
  change AspisR1.naturalEval f
      (algebraMap (ZMod P) E (storedLine16X parent)) = _
  rw [hpoint]
  unfold AspisR1.naturalEval
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← map_naturalLineValue iota
    (algebraMap (ZMod P) K (storedLine16X parent)) j.val]

#print axioms map_doubledFactor
#print axioms map_naturalLineValue
#print axioms map_algebraMap_prime
#print axioms secondEncoder_query_eq_natural_sum

end AspisR1.NaturalEmbedding
end
