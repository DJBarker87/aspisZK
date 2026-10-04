import AspisV8R19.R421UniformMasked31Block
import Mathlib.Tactic

/-! A uniform finite-tape fact for the first four masked 31-bit words.
This is only the marginal mean of the one-block event. -/
set_option autoImplicit false
namespace AspisV8R19.R551FirstFourZeroBlock

open DuplexFrames SourceDuplexStep SamplerWords OracleResampling
open R421UniformMasked31Block
noncomputable section

def firstFourZero (block : State) : Prop :=
  ∀ j : Fin 4, masked 31 (word block ⟨j.val, by omega⟩) = 0

def splitFin8Four {A : Type} : (Fin 8 → A) ≃
    ((Fin 4 → A) × (Fin 4 → A)) where
  toFun f :=
    (fun j => f ⟨j.val, by omega⟩,
     fun j => f ⟨4 + j.val, by omega⟩)
  invFun p i :=
    if h : i.val < 4 then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - 4, by omega⟩
  left_inv f := by
    funext i
    by_cases h : i.val < 4
    · simp [h]
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · funext j
      simp [Fin.ext_iff]
    · funext j
      simp [Fin.ext_iff]

def lowFourZero (f : Fin 4 → Fin (2^31)) : Prop :=
  ∀ j : Fin 4, f j = 0

theorem lowFourZero_mean :
    OracleResampling.mean (fun f : Fin 4 → Fin (2^31) =>
      if lowFourZero f then (1 : ℚ) else 0) =
      (1 / (2^31 : ℚ)) ^ 4 := by
  have hone f : lowFourZero f ↔ f = 0 := by
    constructor
    · intro hf
      funext j
      exact hf j
    · intro hf j
      simpa [hf]
  have hsum : ∑ f : Fin 4 → Fin (2^31),
      (if f = 0 then (1 : ℚ) else 0) = 1 := by
    simp
  unfold OracleResampling.mean
  have hcard : Fintype.card (Fin 4 → Fin (2^31)) = (2^31)^4 := by
    simp [Fintype.card_fun]
  have hden : ((Fintype.card (Fin 4 → Fin (2^31)) : ℚ)) =
      (2^31 : ℚ)^4 := by
    rw [hcard]
    push_cast
  have hpos : (2^31 : ℚ) ≠ 0 := by positivity
  rw [← hone]
  simp only [if_congr]
  rw [hsum, hden]
  field_simp

theorem firstFourZero_mean :
    OracleResampling.mean (fun block : State =>
      if firstFourZero block then (1 : ℚ) else 0) =
      (1 / (2^31 : ℚ)) ^ 4 := by
  have htransport : OracleResampling.mean (fun block : State =>
      if firstFourZero block then (1 : ℚ) else 0) =
      OracleResampling.mean (fun p : (Fin 8 → Fin 2) ×
          (Fin 8 → Fin (2^31)) =>
        if ∀ j : Fin 4, p.2 ⟨j.val, by omega⟩ = 0 then (1 : ℚ) else 0) := by
    rw [mean_equiv splitBlock31Equiv]
    apply mean_congr
    intro block
    have hz : firstFourZero block ↔ ∀ j : Fin 4,
        ((splitBlock31Equiv block).2) ⟨j.val, by omega⟩ = 0 := by
      simp [firstFourZero, masked31_value]
    simp only [hz]
  rw [htransport, mean_prod]
  have hfirst : OracleResampling.mean (fun f : Fin 8 → Fin (2^31) =>
      if ∀ j : Fin 4, f ⟨j.val, by omega⟩ = 0 then (1 : ℚ) else 0) =
      (1 / (2^31 : ℚ)) ^ 4 := by
    rw [mean_equiv splitFin8Four]
    rw [mean_prod]
    have hsecond : OracleResampling.mean (fun _ : Fin 4 → Fin (2^31) =>
        (1 : ℚ)) = 1 := mean_const _
    rw [hsecond]
    have hfirst' : OracleResampling.mean (fun f : Fin 4 → Fin (2^31) =>
        if lowFourZero f then (1 : ℚ) else 0) =
        (1 / (2^31 : ℚ)) ^ 4 := lowFourZero_mean
    apply mean_congr
    intro p
    have hp : (∀ j : Fin 4,
        (splitFin8Four.symm p) ⟨j.val, by omega⟩ = 0) ↔ lowFourZero p.1 := by
      constructor
      · intro h j
        simpa [splitFin8Four] using h j
      · intro h j
        simpa [splitFin8Four] using h j
    simp only [hp]
    exact hfirst'
  rw [mean_prod]
  have hbits : OracleResampling.mean (fun _ : Fin 8 → Fin 2 => (1 : ℚ)) = 1 :=
    mean_const _
  rw [hbits, hfirst]

#print axioms splitFin8Four
#print axioms lowFourZero_mean
#print axioms firstFourZero_mean

end
end AspisV8R19.R551FirstFourZeroBlock
