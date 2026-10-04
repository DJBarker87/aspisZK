import AspisV8R19.R421UniformMasked31Block
import Mathlib.Tactic
/-! Exact marginal mean for one uniform 32-byte block only. -/
set_option autoImplicit false
namespace AspisV8R19.R551FirstFourZeroBlockV4
open DuplexFrames SourceDuplexStep SamplerWords OracleResampling
open R421UniformMasked31Block
noncomputable section
def modulus : Nat := 2^31
noncomputable def indicator (p : Prop) : ℚ := by classical exact if p then 1 else 0
def z31 : Fin modulus := ⟨0, by norm_num [modulus]⟩
def zeroFn4 : Fin 4 → Fin modulus := fun _ => z31
def firstFourZero (block : State) : Prop := ∀ j : Fin 4, masked 31 (word block ⟨j.val, by omega⟩) = 0
def lowFourZero (f : Fin 4 → Fin modulus) : Prop := ∀ j, f j = z31

theorem mean_singleton {A : Type} [Fintype A] [Nonempty A] [DecidableEq A] (a : A) :
    mean (fun x : A => indicator (x = a)) = 1 / (Fintype.card A : ℚ) := by
  classical
  unfold mean
  change (∑ x : A, (if x = a then (1:ℚ) else 0)) / (Fintype.card A : ℚ) = _
  have hs : (∑ x : A, if x = a then (1:ℚ) else 0) = 1 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      simp [hba]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  rw [hs]

def splitFin8Four {A : Type} : (Fin 8 → A) ≃ ((Fin 4 → A) × (Fin 4 → A)) where
  toFun f := (fun j => f ⟨j.val, by omega⟩, fun j => f ⟨4 + j.val, by omega⟩)
  invFun p i := if h : i.val < 4 then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - 4, by omega⟩
  left_inv f := by
    funext i
    dsimp
    split
    · rfl
    · congr 1
      apply Fin.ext
      have hi := i.isLt
      omega
  right_inv p := by
    apply Prod.ext
    · funext j
      change (if j.val < 4 then p.1 ⟨j.val, j.isLt⟩ else p.2 ⟨j.val - 4, by omega⟩) = p.1 j
      simp [j.isLt]
    · funext j
      change (if 4 + j.val < 4 then p.1 ⟨4 + j.val, by omega⟩ else p.2 ⟨4 + j.val - 4, by omega⟩) = p.2 j
      have hj : ¬ (4 + j.val < 4) := by omega
      rw [if_neg hj]
      congr 1
      apply Fin.ext
      have := j.isLt
      omega

theorem lowFourZero_mean :
    mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) = (1 / (modulus : ℚ)) ^ 4 := by
  classical
  haveI : Nonempty (Fin 4 → Fin modulus) := ⟨zeroFn4⟩
  have hu (f : Fin 4 → Fin modulus) : lowFourZero f ↔ f = zeroFn4 := by
    constructor
    · intro h
      funext j
      exact h j
    · intro h j
      simpa [zeroFn4] using congrFun h j
  rw [mean_congr (fun f => congrArg indicator (propext (hu f)))]
  rw [mean_singleton]
  have hc : Fintype.card (Fin 4 → Fin modulus) = modulus ^ 4 := by simp
  rw [hc, Nat.cast_pow]
  ring

theorem firstFourZero_mean :
    mean (fun block : State => indicator (firstFourZero block)) = (1 / (modulus : ℚ)) ^ 4 := by
  classical
  have hblock : mean (fun block : State => indicator (firstFourZero block)) =
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
          simpa [z31] using congrArg Fin.val hj
      _ = _ := mean_equiv splitBlock31Equiv _
  rw [hblock]
  haveI : Nonempty (Fin 8 → Fin 2) := ⟨fun _ => 0⟩
  have hfield : mean (fun f : Fin 8 → Fin modulus => indicator
      (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31)) = (1 / (modulus : ℚ)) ^ 4 := by
    have htransport : mean (fun f : Fin 8 → Fin modulus => indicator
        (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31)) =
        mean (fun p : (Fin 4 → Fin modulus) × (Fin 4 → Fin modulus) => indicator (lowFourZero p.1)) := by
      calc
        _ = mean (fun f : Fin 8 → Fin modulus => indicator (lowFourZero (splitFin8Four f).1)) := by
          apply mean_congr
          intro f
          apply congrArg indicator
          rfl
        _ = _ := mean_equiv splitFin8Four _
    rw [htransport]
    haveI : Nonempty (Fin 4 → Fin modulus) := ⟨zeroFn4⟩
    calc
      mean (fun p : (Fin 4 → Fin modulus) × (Fin 4 → Fin modulus) => indicator (lowFourZero p.1))
          = mean (fun f : Fin 4 → Fin modulus => mean (fun _ : Fin 4 → Fin modulus => indicator (lowFourZero f))) := by
            exact mean_prod (fun f _ => indicator (lowFourZero f))
      _ = mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) := by simp [mean_const]
      _ = _ := lowFourZero_mean
  calc
    _ = mean (fun _ : Fin 8 → Fin 2 => mean (fun f : Fin 8 → Fin modulus =>
        indicator (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31))) := by
          exact mean_prod (X := Fin 8 → Fin 2) (Y := Fin 8 → Fin modulus) _
    _ = _ := by simp [hfield, mean_const]

#print axioms mean_singleton
#print axioms splitFin8Four
#print axioms lowFourZero_mean
#print axioms firstFourZero_mean
end
end AspisV8R19.R551FirstFourZeroBlockV4
