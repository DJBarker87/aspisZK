import ExactFoldRecovery

/-! Four evaluations in an arbitrary submodule recover all four coefficients.
Reuse the existing code-valued Lagrange theorem by pulling the target
submodule back to K^4 through the actual linear-combination map. No basis,
finite dimensionality, nonzero nodes or concrete characteristic is assumed.
This is deterministic interpolation, not a challenge-probability theorem. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.FourPointSubmodule
open Polynomial Finset
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def combine (w : Fin 4 → M) : (Fin 4 → K) →ₗ[K] M where
  toFun c := ∑ i : Fin 4,c i • w i
  map_add' c d := by
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul,RingHom.id_apply]

theorem combine_monomial_coefficient (w : Fin 4 → M) (j : Fin 4) :
    combine w (fun i : Fin 4=>(X^i.val:K[X]).coeff j.val)=w j := by
  have coefficient (i : Fin 4) : (X^i.val:K[X]).coeff j.val=
      if i=j then 1 else 0 := by
    by_cases same : i=j
    · simp [same]
    · have different : i.val≠j.val := fun h=>same (Fin.ext h)
      simp [Polynomial.coeff_X_pow,same,different,Ne.symm different]
  simp only [combine,LinearMap.coe_mk,AddHom.coe_mk]
  simp_rw [coefficient]
  simp

/-- The Finset supplies distinctness: it contains exactly four different
field elements. The vectors and the target submodule are fixed throughout
these four evaluations. -/
theorem four_evaluations_recover (S : Submodule K M) (w : Fin 4 → M)
    (nodes : Finset K) (four : nodes.card=4)
    (inside : ∀ a∈nodes,(∑ i : Fin 4,a^i.val • w i)∈S) (j : Fin 4) :
    w j∈S := by
  classical
  let pulled := S.comap (combine w)
  have insidePulled (a : K) (ha : a∈nodes) :
      (fun i : Fin 4=>(X^i.val:K[X]).eval a)∈pulled := by
    change combine w (fun i : Fin 4=>(X^i.val:K[X]).eval a)∈S
    simpa only [combine,LinearMap.coe_mk,AddHom.coe_mk,Polynomial.eval_pow,
      Polynomial.eval_X] using inside a ha
  have degree (i : Fin 4) : (X^i.val:K[X]).natDegree≤3 := by
    simp only [Polynomial.natDegree_X_pow]
    omega
  have recovered:=AspisV8.ExactFoldRecovery.four_code_evaluations_recover_coefficients
    pulled (fun i : Fin 4=>(X^i.val:K[X])) nodes four degree insidePulled j.val
  change combine w (fun i : Fin 4=>(X^i.val:K[X]).coeff j.val)∈S at recovered
  rwa [combine_monomial_coefficient] at recovered

/-- Convenient vector interface. Injectivity of the supplied four nodes is
the only distinctness premise; zero is a legal interpolation node. -/
theorem four_distinct_evaluations_recover (S : Submodule K M) (w : Fin 4 → M)
    (nodes : Fin 4 → K) (distinct : Function.Injective nodes)
    (inside : ∀ a : Fin 4,(∑ i : Fin 4,(nodes a)^i.val • w i)∈S) :
    ∀ j : Fin 4,w j∈S := by
  classical
  let selected := Finset.univ.image nodes
  have four : selected.card=4 := by
    rw [Finset.card_image_iff.mpr (fun _ _ _ _ h=>distinct h)]
    exact Finset.card_fin 4
  intro j
  apply four_evaluations_recover S w selected four
  intro a ha
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
  exact inside i

def cubicValue (w : Fin 4 → M) (a : K) : M :=
  w 0+a • w 1+a^2 • w 2+a^3 • w 3

theorem sum_is_literal_cubic (w : Fin 4 → M) (a : K) :
    (∑ i : Fin 4,a^i.val • w i)=cubicValue w a := by
  rw [Fin.sum_univ_four]
  have three : (3:Fin 4).val=3 := rfl
  simp only [cubicValue,Fin.val_zero,Fin.val_one,Fin.val_two,three,
    pow_zero,pow_one,one_smul]

/-- Literal scalar-power endpoint needed by the denominator-cleared chord
argument. Nothing is assumed about the four coefficient vectors individually. -/
theorem literal_cubic_four_points (S : Submodule K M) (w : Fin 4 → M)
    (nodes : Fin 4 → K) (distinct : Function.Injective nodes)
    (inside : ∀ a : Fin 4,
      w 0+(nodes a) • w 1+(nodes a)^2 • w 2+(nodes a)^3 • w 3∈S) :
    ∀ j : Fin 4,w j∈S := by
  apply four_distinct_evaluations_recover S w nodes distinct
  intro a
  rw [sum_is_literal_cubic]
  exact inside a

#print axioms combine_monomial_coefficient
#print axioms four_evaluations_recover
#print axioms four_distinct_evaluations_recover
#print axioms sum_is_literal_cubic
#print axioms literal_cubic_four_points
end
end AspisV8.FourPointSubmodule
