import R0Z.StatisticalDistance

/-! Uniform affine laws over abstract finite vector spaces. All cardinalities
are transported through equivalences. No concrete tape, row or trace universe
is evaluated. Finite-dimensional spaces over a finite field supply these
Fintype instances; the argument needs only their finiteness. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.AffineLaw
attribute [local instance] Classical.propDecidable

variable {k T T' V : Type} [Field k]
  [AddCommGroup T] [Module k T] [Fintype T]
  [AddCommGroup T'] [Module k T'] [Fintype T']
  [AddCommGroup V] [Module k V] [Fintype V]

def coset (A : T →ₗ[k] V) (b : V) : Set V := {v | v-b ∈ LinearMap.range A}

/-- A nonempty fibre is a translate of the kernel. -/
def fibreEquivKer (A : T →ₗ[k] V) (b v : V) (r₀ : T) (hr₀ : b+A r₀=v) :
    {r : T // b+A r=v} ≃ LinearMap.ker A where
  toFun r := ⟨r.1-r₀, by
    change A (r.1-r₀) = 0
    rw [map_sub, sub_eq_zero]
    exact add_left_cancel (r.2.trans hr₀.symm)⟩
  invFun r := ⟨r.1+r₀, by
    have hr : A r.1 = 0 := r.2
    rw [map_add, hr, zero_add, hr₀]⟩
  left_inv r := Subtype.ext (sub_add_cancel _ _)
  right_inv r := Subtype.ext (add_sub_cancel_right _ _)

/-- Translation identifies the affine coset with the range. -/
def cosetEquivRange (A : T →ₗ[k] V) (b : V) : coset A b ≃ LinearMap.range A where
  toFun v := ⟨v.1-b, v.2⟩
  invFun v := ⟨v.1+b, by simpa only [coset, Set.mem_setOf_eq, add_sub_cancel_right] using v.2⟩
  left_inv v := Subtype.ext (sub_add_cancel _ _)
  right_inv v := Subtype.ext (add_sub_cancel_right _ _)

/-- Cardinality from the quotient/kernel product and the first isomorphism
 theorem, not enumeration of either space. -/
theorem card_tape (A : T →ₗ[k] V) :
    Fintype.card T = Fintype.card (LinearMap.ker A) * Fintype.card (LinearMap.range A) := by
  have h := (LinearMap.ker A).card_eq_card_quotient_mul_card
  rw [Nat.card_congr A.quotKerEquivRange.toEquiv] at h
  simpa only [Nat.card_eq_fintype_card] using h

theorem law_eq_fibre_card {R U : Type} [Fintype R] (f : R → U) (v : U) :
    law f v = (Fintype.card {r : R // f r=v} : ℚ) / Fintype.card R := by
  classical
  simp [law, mean, Fintype.card_subtype, Finset.sum_boole]

/-- The pushforward is uniform on b + range A, and zero off that coset. -/
theorem uniform_coset (A : T →ₗ[k] V) (b v : V) :
    law (fun r => b+A r) v = if v ∈ coset A b then
      (1 : ℚ) / Fintype.card (coset A b) else 0 := by
  classical
  by_cases hv : v ∈ coset A b
  · have hex : ∃ r₀, A r₀ = v-b := hv
    obtain ⟨r₀, hr₀⟩ := hex
    have he : b + A r₀ = v := by rw [hr₀]; abel
    rw [if_pos hv, law_eq_fibre_card,
      Fintype.card_congr (fibreEquivKer A b v r₀ he),
      Fintype.card_congr (cosetEquivRange A b), card_tape A, Nat.cast_mul]
    have hk : (Fintype.card (LinearMap.ker A) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hi : (Fintype.card (LinearMap.range A) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  · have hn : ∀ r, b+A r ≠ v := by
      intro r he
      apply hv
      refine ⟨r, ?_⟩
      rw [← he]
      abel
    simp only [if_neg hv, law, mean, if_neg (hn _), Finset.sum_const_zero, zero_div]

/-- The equal-coset corollary permits different finite tape spaces and maps. -/
theorem equal_cosets_law (A : T →ₗ[k] V) (A' : T' →ₗ[k] V) (b b' : V)
    (h : coset A b = coset A' b') :
    EqualLaws (fun r => b+A r) (fun r => b'+A' r) := by
  intro v
  rw [uniform_coset, uniform_coset, h]

/-- D4′'s range equality and zero-tape displacement imply equal cosets. -/
theorem coset_eq_of_range_eq_displacement (A : T →ₗ[k] V) (A' : T' →ₗ[k] V)
    (b b' : V) (hr : LinearMap.range A = LinearMap.range A')
    (hd : b-b' ∈ LinearMap.range A) : coset A b = coset A' b' := by
  ext v
  change (v-b ∈ LinearMap.range A) ↔ (v-b' ∈ LinearMap.range A')
  rw [← hr]
  constructor
  · intro hv
    convert (LinearMap.range A).add_mem hv hd using 1 <;> abel
  · intro hv
    convert (LinearMap.range A).sub_mem hv hd using 1 <;> abel

theorem equal_laws_of_mask_image (A : T →ₗ[k] V) (A' : T' →ₗ[k] V) (b b' : V)
    (hr : LinearMap.range A = LinearMap.range A')
    (hd : b-b' ∈ LinearMap.range A) :
    EqualLaws (fun r => b+A r) (fun r => b'+A' r) :=
  equal_cosets_law A A' b b' (coset_eq_of_range_eq_displacement A A' b b' hr hd)

/-- Carry public, constant metadata along with a field-payload law. -/
theorem equal_laws_const_pair {R S U M : Type} [Fintype R] [Fintype S]
    (f : R → U) (g : S → U) (m : M) (h : EqualLaws f g) :
    EqualLaws (fun r => (m, f r)) (fun s => (m, g s)) := by
  classical
  rintro ⟨m',v⟩
  by_cases hm : m=m'
  · subst m'
    simpa only [law, mean, Prod.mk.injEq, true_and] using h v
  · simp only [law, mean, Prod.mk.injEq, hm, false_and, if_false,
      Finset.sum_const_zero, zero_div]

/-- Product counting measure is independent uniform sampling of both tapes. -/
theorem law_product {E R U : Type} [Fintype E] [Fintype R]
    (f : E × R → U) (v : U) :
    law f v = mean (fun e => law (fun r => f (e,r)) v) := by
  classical
  simp only [law, mean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  rw [← Finset.sum_div]
  ring

/-- Marginalising any nonempty uniform independent eligible-noise tape preserves
an equal conditional law. Neither the noise nor the tape is enumerated. -/
theorem marginalisation {E R S U : Type} [Fintype E] [Nonempty E]
    [Fintype R] [Fintype S] (f : E × R → U) (g : S → U)
    (h : ∀ e, EqualLaws (fun r => f (e,r)) g) : EqualLaws f g := by
  intro v
  rw [law_product]
  simp only [h _ v, mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card E : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

#print axioms fibreEquivKer
#print axioms card_tape
#print axioms uniform_coset
#print axioms equal_cosets_law
#print axioms equal_laws_of_mask_image
#print axioms marginalisation
end R0Z.AffineLaw
