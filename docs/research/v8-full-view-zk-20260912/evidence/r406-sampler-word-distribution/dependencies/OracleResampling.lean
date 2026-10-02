import AspisV8R17.AdaptiveOracle
import Mathlib.Tactic

/-! Uniform finite-oracle resampling by a concrete swap bijection.
No assumption that an adaptive execution never repeats an address. -/
set_option autoImplicit false
namespace AspisV8R19.OracleResampling
noncomputable section
variable {X Y I A : Type*}

def mean [Fintype X] (f : X → ℚ) : ℚ := (∑ x, f x) / Fintype.card X

theorem mean_congr [Fintype X] {f g : X → ℚ} (h : ∀ x, f x = g x) :
    mean f = mean g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl (fun x _ => h x)

theorem mean_const [Fintype X] [Nonempty X] (c : ℚ) : mean (fun _ : X => c) = c := by
  have hn : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hn]

theorem mean_equiv [Fintype X] [Fintype Y] (e : X ≃ Y) (f : Y → ℚ) :
    mean (fun x => f (e x)) = mean f := by
  unfold mean
  rw [Equiv.sum_comp e, Fintype.card_congr e]

theorem mean_prod [Fintype X] [Fintype Y] (f : X → Y → ℚ) :
    mean (fun p : X × Y => f p.1 p.2) = mean (fun x => mean (f x)) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.sum_div, div_div]
  congr 1
  ring

theorem mean_comm [Fintype X] [Fintype Y] (f : X → Y → ℚ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  rw [← mean_prod, ← mean_prod]
  exact (mean_equiv (Equiv.prodComm Y X) (fun p : X × Y => f p.1 p.2)).symm

def swapCell [DecidableEq I] (i : I) : ((I → A) × A) ≃ ((I → A) × A) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    apply Prod.ext
    · funext j
      by_cases h : j = i <;> simp [h, Function.update_of_ne]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext j
      by_cases h : j = i <;> simp [h, Function.update_of_ne]
    · simp

theorem resample_cell [Fintype I] [Fintype A] [Nonempty A] [DecidableEq I]
    (i : I) (f : (I → A) → ℚ) :
    mean f = mean (fun a => mean (fun H => f (Function.update H i a))) := by
  have h := mean_equiv (swapCell (A := A) i) (fun p : (I → A) × A => f p.1)
  change mean (fun p : (I → A) × A => f (Function.update p.1 i p.2)) =
    mean (fun p : (I → A) × A => f p.1) at h
  rw [mean_prod (fun H a => f (Function.update H i a)),
    mean_prod (fun (H : I → A) (_ : A) => f H)] at h
  simp only [mean_const] at h
  rw [mean_comm] at h
  exact h.symm

#print axioms mean_congr
#print axioms mean_const
#print axioms mean_equiv
#print axioms mean_prod
#print axioms mean_comm
#print axioms swapCell
#print axioms resample_cell
end
end AspisV8R19.OracleResampling
