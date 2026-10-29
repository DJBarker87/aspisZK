import R0Z.AffineLaw

/-! D12's fixed-N coset argument and independent-uniform mixture. These are
abstract finite-space facts; no concrete cardinality or rank is computed. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.AbsorptionLaw
attribute [local instance] Classical.propDecidable

theorem law_equiv {R S V : Type} [Fintype R] [Fintype S]
    (e : R ≃ S) (f : S → V) : EqualLaws (fun r => f (e r)) f := by
  intro v
  simp only [law, mean, Fintype.card_congr e]
  exact congrArg (fun q : ℚ => q / Fintype.card S)
    (e.sum_comp (fun s => if f s = v then (1 : ℚ) else 0))

theorem equal_laws_of_equiv {R S V : Type} [Fintype R] [Fintype S]
    (e : R ≃ S) (f g : S → V)
    (h : EqualLaws (fun r => f (e r)) (fun r => g (e r))) : EqualLaws f g := by
  intro v
  exact (law_equiv e f v).symm.trans ((h v).trans (law_equiv e g v))

theorem law_product_right {M N V : Type} [Fintype M] [Fintype N]
    (f : M × N → V) (v : V) :
    law f v = mean (fun n => law (fun m => f (m,n)) v) := by
  rw [← law_equiv (Equiv.prodComm N M) f v, AffineLaw.law_product]
  rfl

variable {k M N V : Type} [Field k]
  [AddCommGroup M] [Module k M] [Fintype M]
  [AddCommGroup N] [Module k N] [Fintype N]
  [AddCommGroup V] [Module k V] [Fintype V]

def pureMap (A : M × N →ₗ[k] V) : M →ₗ[k] V := A.comp (LinearMap.inl k M N)

theorem split (A : M × N →ₗ[k] V) (m : M) (n : N) :
    A (m,n) = pureMap A m + A (0,n) := by
  change A (m,n) = A (m,0) + A (0,n)
  rw [← map_add]
  simp

/-- (i) removes the remainder within each fixed-N affine coset. -/
theorem fixed_n (A : M × N →ₗ[k] V) (c : V) (g : N → V) (n : N)
    (hg : g n ∈ LinearMap.range (pureMap A)) :
    EqualLaws (fun m => c + A (m,n) + g n) (fun m => c + A (m,n)) := by
  have hd : (c + A (0,n) + g n) - (c + A (0,n)) ∈ LinearMap.range (pureMap A) := by
    convert hg using 1 <;> abel
  have hh := AffineLaw.equal_laws_of_mask_image (pureMap A) (pureMap A)
    (c + A (0,n) + g n) (c + A (0,n)) rfl hd
  have he : (fun m => c + A (m,n) + g n) =
      (fun m => c + A (0,n) + g n + pureMap A m) := by
    funext m; rw [split]; abel
  have hf : (fun m => c + A (m,n)) =
      (fun m => c + A (0,n) + pureMap A m) := by
    funext m; rw [split]; abel
  rw [he, hf]
  exact hh

/-- Mixing over independent uniform N gives precisely the linear pushforward. -/
theorem mixture (A : M × N →ₗ[k] V) (c : V) (g : N → V)
    (hg : ∀ n, g n ∈ LinearMap.range (pureMap A)) :
    EqualLaws (fun t : M × N => c + A t + g t.2) (fun t => c + A t) := by
  intro v
  rw [law_product_right, law_product_right]
  simp only [fixed_n A c g _ (hg _) v]

/-- The common mixture is uniform on c + range A. -/
theorem uniform_coset (A : M × N →ₗ[k] V) (c : V) (g : N → V)
    (hg : ∀ n, g n ∈ LinearMap.range (pureMap A)) (v : V) :
    law (fun t : M × N => c + A t + g t.2) v =
      if v ∈ AffineLaw.coset A c then
        (1 : ℚ) / Fintype.card (AffineLaw.coset A c) else 0 := by
  rw [mixture A c g hg v, AffineLaw.uniform_coset]

#print axioms equal_laws_of_equiv
#print axioms law_equiv
#print axioms fixed_n
#print axioms mixture
#print axioms uniform_coset
end R0Z.AbsorptionLaw
