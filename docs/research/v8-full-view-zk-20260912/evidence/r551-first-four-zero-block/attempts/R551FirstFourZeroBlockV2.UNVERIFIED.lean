import AspisV8R19.R421UniformMasked31Block
import Mathlib.Tactic

/-! Exact one-block mean for the event that the first four masked words vanish.
This is a single uniform State, not a shared-oracle freshness claim. -/
set_option autoImplicit false
namespace AspisV8R19.R551FirstFourZeroBlockV2
open DuplexFrames SourceDuplexStep SamplerWords OracleResampling
open R421UniformMasked31Block
noncomputable section

def modulus : Nat := 2^31
def indicator (p : Prop) : ℚ := if p then 1 else 0
def z31 : Fin modulus := ⟨0, by norm_num [modulus]⟩
def zeroFn4 : Fin 4 → Fin modulus := fun _ => z31
def firstFourZero (block : State) : Prop :=
  ∀ j : Fin 4, masked 31 (word block ⟨j.val, by omega⟩) = 0
def lowFourZero (f : Fin 4 → Fin modulus) : Prop := ∀ j, f j = z31

def splitFin8Four {A : Type} : (Fin 8 → A) ≃ ((Fin 4 → A) × (Fin 4 → A)) where
  toFun f := (fun j => f ⟨j.val, by omega⟩, fun j => f ⟨4 + j.val, by omega⟩)
  invFun p i := if h : i.val < 4 then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - 4, by omega⟩
  left_inv f := by
    funext i
    simp only
    split
    · rfl
    · congr 1
      apply Fin.ext
      simp
  right_inv p := by
    apply Prod.ext <;> funext j
    · simp [splitFin8Four]
    · simp [splitFin8Four]

theorem lowFourZero_mean :
    mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) =
      (1 / (modulus : ℚ)) ^ 4 := by
  classical
  have hu (f : Fin 4 → Fin modulus) : lowFourZero f ↔ f = zeroFn4 := by
    constructor
    · intro h
      funext j
      exact h j
    · intro h j
      simpa [zeroFn4] using congrFun h j
  unfold mean
  simp only [indicator, Fintype.card_fun, Fintype.card_fin]
  have hs : (∑ f : Fin 4 → Fin modulus, if f = zeroFn4 then (1:ℚ) else 0) = 1 := by
    rw [Finset.sum_eq_single zeroFn4]
    · simp
    · intro b hb hne
      simp [hne]
    · intro h
      exact (h (by simp [zeroFn4])).elim
  have hh : (∑ f : Fin 4 → Fin modulus, if lowFourZero f then (1:ℚ) else 0) = 1 := by
    apply Finset.sum_congr rfl
    intro f _
    rw [hu]
  rw [hh]
  norm_num [modulus]

theorem firstFourZero_mean :
    mean (fun block : State => indicator (firstFourZero block)) =
      (1 / (modulus : ℚ)) ^ 4 := by
  classical
  have hstate : mean (fun block : State => indicator (firstFourZero block)) =
      mean (fun p : (Fin 8 → Fin 2) × (Fin 8 → Fin modulus) =>
        indicator (∀ j : Fin 4, p.2 ⟨j.val, by omega⟩ = z31)) := by
    calc
      _ = mean (fun block : State => indicator
          (∀ j : Fin 4, ((splitBlock31Equiv block).2) ⟨j.val, by omega⟩ = z31)) := by
        apply mean_congr
        intro block
        apply congrArg indicator
        constructor
        · intro h j
          rw [masked31_value]
          exact Fin.ext (by simpa [z31] using h j)
        · intro h j
          have hj := h j
          rw [masked31_value] at hj
          have : ((splitBlock31Equiv block).2) ⟨j.val, by omega⟩ = z31 := hj
          simpa [z31] using congrArg Fin.val this
      _ = _ := mean_equiv splitBlock31Equiv _
  rw [hstate, mean_prod]
  have hlow : mean (fun f : Fin 8 → Fin modulus =>
      indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31)) =
      (1 / (modulus : ℚ)) ^ 4 := by
    have ht := mean_equiv splitFin8Four
      (fun p : (Fin 4 → Fin modulus) × (Fin 4 → Fin modulus) => indicator (lowFourZero p.1))
    have hc : mean (fun f : Fin 8 → Fin modulus =>
        indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31)) =
        mean (fun p : (Fin 4 → Fin modulus) × (Fin 4 → Fin modulus) =>
          indicator (lowFourZero p.1)) := by
      calc
        _ = mean (fun f : Fin 8 → Fin modulus => indicator (lowFourZero (splitFin8Four f).1)) := by
          apply mean_congr
          intro f
          apply congrArg indicator
          rfl
        _ = _ := ht
    rw [hc, mean_prod]
    change mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) = _
    exact lowFourZero_mean
  rw [mean_prod]
  change mean (fun _ : Fin 8 → Fin 2 =>
      mean (fun f : Fin 8 → Fin modulus =>
        indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31))) = _
  simp [hlow, mean_const]

#print axioms splitFin8Four
#print axioms lowFourZero_mean
#print axioms firstFourZero_mean
end
end AspisV8R19.R551FirstFourZeroBlockV2
