import AspisV8R19.R421UniformMasked31Block
import Mathlib.Tactic

/-! Exact marginal mean of the first-four-zero event for one uniform 32-byte
block. This says nothing about successive shared-oracle blocks. -/
set_option autoImplicit false
namespace AspisV8R19.R551FirstFourZeroBlock

open DuplexFrames SourceDuplexStep SamplerWords OracleResampling
open R421UniformMasked31Block
noncomputable section

def modulus : Nat := 2^31
def indicator (p : Prop) : ℚ := @ite ℚ p (Classical.propDecidable p) 1 0
def zeroFn4 : Fin 4 → Fin modulus := fun _ => (0 : Fin modulus)

def firstFourZero (block : State) : Prop :=
  ∀ j : Fin 4, masked 31 (word block ⟨j.val, by omega⟩) = 0

def lowFourZero (f : Fin 4 → Fin modulus) : Prop :=
  ∀ j : Fin 4, f j = (0 : Fin modulus)

def splitFin8Four {A : Type} : (Fin 8 → A) ≃
    ((Fin 4 → A) × (Fin 4 → A)) where
  toFun f := (fun j => f ⟨j.val, by omega⟩, fun j => f ⟨4 + j.val, by omega⟩)
  invFun p i :=
    if h : i.val < 4 then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - 4, by omega⟩
  left_inv f := by
    funext i
    change (if i.val < 4 then f ⟨i.val, by omega⟩
      else f ⟨4 + (i.val - 4), by omega⟩) = f i
    by_cases h : i.val < 4
    · simp [h]
    · simp only [if_neg h]
      apply congrArg f
      apply Fin.ext
      have hi := i.isLt
      omega
  right_inv p := by
    apply Prod.ext
    · funext j
      simp [splitFin8Four]
    · funext j
      simp [splitFin8Four]

theorem lowFourZero_mean :
    OracleResampling.mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) =
      (1 / (modulus : ℚ)) ^ 4 := by
  classical
  have huniq (f : Fin 4 → Fin modulus) : lowFourZero f ↔ f = zeroFn4 := by
    constructor
    · intro h
      funext j
      exact h j
    · intro h j
      simpa [zeroFn4] using congrFun h j
  have hcongr : OracleResampling.mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) =
      OracleResampling.mean (fun f : Fin 4 → Fin modulus => if f = zeroFn4 then (1:ℚ) else 0) := by
    apply mean_congr
    intro f
    by_cases h : lowFourZero f <;> simp [indicator, h, huniq f, zeroFn4]
  rw [hcongr]
  unfold OracleResampling.mean
  simp only [Fintype.card_fun, Fintype.card_fin]
  simp
  ring

theorem firstFourZero_mean :
    OracleResampling.mean (fun block : State => indicator (firstFourZero block)) =
      (1 / (modulus : ℚ)) ^ 4 := by
  classical
  have hblock : OracleResampling.mean (fun block : State => indicator (firstFourZero block)) =
      OracleResampling.mean (fun p : (Fin 8 → Fin 2) × (Fin 8 → Fin modulus) =>
        indicator (∀ j : Fin 4, p.2 ⟨j.val, by omega⟩ = 0)) := by
    calc
      _ = OracleResampling.mean (fun block : State =>
          indicator (∀ j : Fin 4, ((splitBlock31Equiv block).2) ⟨j.val, by omega⟩ = 0)) := by
            apply mean_congr
            intro block
            apply congrArg indicator
            constructor
            · intro h j
              have hj := h j
              rw [masked31_value]
              exact hj
            · intro h j
              have hj := h j
              rw [masked31_value] at hj
              exact hj
      _ = _ := (mean_equiv splitBlock31Equiv _).symm
  rw [hblock]
  rw [mean_prod (fun (_ : Fin 8 → Fin 2) (f : Fin 8 → Fin modulus) =>
    indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = 0))]
  have hfirst : OracleResampling.mean (fun f : Fin 8 → Fin modulus =>
      indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = 0)) = (1 / (modulus : ℚ)) ^ 4 := by
    have hequiv := mean_equiv splitFin8Four
      (fun p : (Fin 4 → Fin modulus) × (Fin 4 → Fin modulus) => indicator (lowFourZero p.1))
    have htransport : OracleResampling.mean (fun f : Fin 8 → Fin modulus =>
        indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = 0)) =
        OracleResampling.mean (fun p : (Fin 4 → Fin modulus) × (Fin 4 → Fin modulus) =>
          indicator (lowFourZero p.1)) := by
      calc
        _ = OracleResampling.mean (fun f : Fin 8 → Fin modulus =>
            indicator (lowFourZero (splitFin8Four f).1)) := by
              apply mean_congr
              intro f
              apply congrArg indicator
              rfl
        _ = _ := hequiv
    rw [htransport]
    rw [mean_prod (fun f (_ : Fin 4 → Fin modulus) => indicator (lowFourZero f))]
    change OracleResampling.mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) = _
    exact lowFourZero_mean
  rw [mean_prod (fun (_ : Fin 8 → Fin 2) (f : Fin 8 → Fin modulus) =>
    indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = 0))]
  change OracleResampling.mean (fun _ : Fin 8 → Fin 2 =>
      OracleResampling.mean (fun f : Fin 8 → Fin modulus =>
        indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = 0))) = _
  simp only [hfirst, mean_const]

#print axioms splitFin8Four
#print axioms lowFourZero_mean
#print axioms firstFourZero_mean

end
end AspisV8R19.R551FirstFourZeroBlock
