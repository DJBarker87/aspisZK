import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-! A cover CONSTRUCTED by interpolation, not a supplied candidate-member
premise. X indexes fibres and Y their scalar slots. The combinatorial leaf
supplies the common support. Code overlap is an explicit code hypothesis. -/
set_option autoImplicit false
namespace AspisV8.NearGammaCover
open Polynomial Finset
variable {K X Y : Type*} [Field K] [DecidableEq K] [DecidableEq X]
  [DecidableEq (Y → K)]

noncomputable def interp (I : Finset K) (c : K → X → Y → K) : X → Y → K[X] :=
  fun x y => Lagrange.interpolate I id (fun g => c g x y)

theorem interp_code_coeff (C : Submodule K (X → Y → K)) (I : Finset K)
    (c : K → X → Y → K) (hc : ∀ g ∈ I, c g ∈ C) (n : ℕ) :
    (fun x y => (interp I c x y).coeff n) ∈ C := by
  classical
  have he : (fun x y => (interp I c x y).coeff n) =
      ∑ g ∈ I, (Lagrange.basis I id g).coeff n • c g := by
    ext x y
    simp [interp, Lagrange.interpolate_apply, coeff_sum, coeff_C_mul,
      Finset.sum_apply, mul_comm]
  rw [he]
  exact C.sum_mem fun g hg => C.smul_mem _ (hc g hg)

theorem interp_eval_code (C : Submodule K (X → Y → K)) (I : Finset K)
    (c : K → X → Y → K) (hc : ∀ g ∈ I, c g ∈ C) (t : K) :
    (fun x y => (interp I c x y).eval t) ∈ C := by
  classical
  have he : (fun x y => (interp I c x y).eval t) =
      ∑ g ∈ I, (Lagrange.basis I id g).eval t • c g := by
    ext x y
    simp [interp, Lagrange.interpolate_apply, eval_finsetSum,
      Finset.sum_apply, mul_comm]
  rw [he]
  exact C.sum_mem fun g hg => C.smul_mem _ (hc g hg)

theorem interp_on_common (I : Finset K) (S : Finset X)
    (v : X → Y → K[X]) (c : K → X → Y → K)
    (degree : ∀ x y, (v x y).degree < I.card)
    (hmatch : ∀ g ∈ I, ∀ x ∈ S, ∀ y, (v x y).eval g = c g x y) :
    ∀ x ∈ S, ∀ y, v x y = interp I c x y := by
  intro x hx y
  exact Lagrange.eq_interpolate_of_eval_eq _ (fun a _ b _ h => h)
    (degree x y) (fun g hg => hmatch g hg x hx y)

/-- Every close codeword is covered, including one selected after t. The
interpolant depends only on I and the already selected nodal codewords. -/
theorem covers_all_near (C : Submodule K (X → Y → K))
    (D S : Finset X) (I : Finset K) (v : X → Y → K[X])
    (c : K → X → Y → K) (B delta : ℕ)
    (hc : ∀ g ∈ I, c g ∈ C) (hSD : S ⊆ D)
    (degree : ∀ x y, (v x y).degree < I.card)
    (hmatch : ∀ g ∈ I, ∀ x ∈ S, ∀ y, (v x y).eval g = c g x y)
    (large : B+delta < S.card)
    (overlap : ∀ u ∈ C, ∀ w ∈ C, u ≠ w →
      (D.filter fun x => u x = w x).card ≤ delta) :
    ∀ t u, u ∈ C → (D.filter fun x => (fun y => (v x y).eval t) ≠ u x).card ≤ B →
      u = fun x y => (interp I c x y).eval t := by
  classical
  intro t u hu near
  let bad := D.filter fun x => (fun y => (v x y).eval t) ≠ u x
  let good := S \ bad
  have hcommon := interp_on_common I S v c degree hmatch
  have hgood : good ⊆ D.filter (fun x => u x = fun y => (interp I c x y).eval t) := by
    intro x hx
    obtain ⟨hs,hbad⟩ := mem_sdiff.mp hx
    have eq : (fun y => (v x y).eval t) = u x := by
      by_contra hn
      exact hbad (mem_filter.mpr ⟨hSD hs,hn⟩)
    apply mem_filter.mpr
    refine ⟨hSD hs, ?_⟩
    rw [← eq]
    funext y
    rw [hcommon x hs y]
  have hcard : delta < good.card := by
    have hs := card_sdiff_add_card_inter S bad
    have hi := card_le_card (inter_subset_right : S ∩ bad ⊆ bad)
    change bad.card ≤ B at near
    dsimp [good]
    omega
  by_contra hne
  have h := overlap u hu _ (interp_eval_code C I c hc t) hne
  have hle := card_le_card hgood
  omega

#print axioms interp_code_coeff
#print axioms interp_on_common
#print axioms covers_all_near
end AspisV8.NearGammaCover
