import AspisV8R19.R421UniformMasked31Block
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R551FirstFourZeroBlockV10
open DuplexFrames SourceDuplexStep SamplerWords OracleResampling
open R421UniformMasked31Block
noncomputable section

def modulus : Nat := 2^31
noncomputable def indicator (p : Prop) : ℚ := by classical exact if p then 1 else 0
def z31 : Fin modulus := ⟨0, by norm_num [modulus]⟩
def zeroFn4 : Fin 4 → Fin modulus := fun _ => z31
def prefixFourEq {A : Type} (a : A) (f : Fin 8 → A) : Prop :=
  ∀ j : Fin 4, f ⟨j.val, by omega⟩ = a
def firstFourZero (block : State) : Prop :=
  ∀ j : Fin 4, masked 31 (word block ⟨j.val, by omega⟩) = 0
def firstFourListZero (xs : List Nat) : Prop := ∀ j : Fin 4, xs[j.val]? = some 0

theorem mean_singleton {A : Type} [Fintype A] [Nonempty A] [DecidableEq A] (a : A) :
    mean (fun x : A => if x = a then (1:ℚ) else 0) = 1 / (Fintype.card A : ℚ) := by
  classical
  unfold mean
  have hs : (∑ x : A, if x = a then (1:ℚ) else 0) = 1 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba; simp [hba]
    · intro ha; exact (ha (Finset.mem_univ a)).elim
  rw [hs]

def splitFin8Four {A : Type} : (Fin 8 → A) ≃ ((Fin 4 → A) × (Fin 4 → A)) where
  toFun f := (fun j => f ⟨j.val, by omega⟩, fun j => f ⟨4 + j.val, by omega⟩)
  invFun p i := if h : i.val < 4 then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - 4, by omega⟩
  left_inv f := by
    funext i
    dsimp
    split
    · rfl
    · apply congrArg f
      apply Fin.ext
      change 4 + (i.val - 4) = i.val
      have hi : 4 ≤ i.val := by omega
      omega
  right_inv p := by
    apply Prod.ext
    · funext j
      dsimp
      simp only [dif_pos j.isLt]
    · funext j
      dsimp
      have hj : ¬ 4 + j.val < 4 := by omega
      simp only [dif_neg hj]
      apply congrArg p.2
      apply Fin.ext
      change 4 + j.val - 4 = j.val
      omega

theorem ofFn_at_four (f : Fin 8 → Nat) (j : Fin 4) :
    (List.ofFn f)[j.val]? = some (f ⟨j.val, by omega⟩) := by
  rw [List.getElem?_ofFn]
  simp only [dif_pos (show j.val < 8 by omega)]

theorem prefixFour_mean {A : Type} [Fintype A] [Nonempty A] [DecidableEq A] (a : A) :
    mean (fun f : Fin 8 → A => indicator (prefixFourEq a f)) =
      (1 / (Fintype.card A : ℚ)) ^ 4 := by
  classical
  haveI : Nonempty (Fin 4 → A) := ⟨fun _ => a⟩
  have hu (f : Fin 4 → A) : (∀ j, f j = a) ↔ f = fun _ => a := by
    constructor
    · intro h; funext j; exact h j
    · intro h j; simpa using congrFun h j
  calc
    mean (fun f : Fin 8 → A => indicator (prefixFourEq a f))
        = mean (fun f : Fin 8 → A => indicator (∀ j : Fin 4, (splitFin8Four f).1 j = a)) := by
          apply mean_congr
          intro f
          apply congrArg indicator
          apply propext
          rfl
    _ = mean (fun p : (Fin 4 → A) × (Fin 4 → A) => indicator (∀ j : Fin 4, p.1 j = a)) :=
          mean_equiv (splitFin8Four (A := A))
            (fun p : (Fin 4 → A) × (Fin 4 → A) => indicator (∀ j : Fin 4, p.1 j = a))
    _ = mean (fun f : Fin 4 → A => indicator (∀ j : Fin 4, f j = a)) := by
          have hmean (f : Fin 4 → A) :
              mean (fun _ : Fin 4 → A => indicator (∀ j : Fin 4, f j = a)) =
                indicator (∀ j : Fin 4, f j = a) := by
            exact mean_const _
          calc
            _ = mean (fun f : Fin 4 → A =>
                  mean (fun _ : Fin 4 → A => indicator (∀ j : Fin 4, f j = a))) :=
                mean_prod (X := Fin 4 → A) (Y := Fin 4 → A)
                  (fun f _ => indicator (∀ j : Fin 4, f j = a))
            _ = _ := by apply mean_congr; intro f; exact hmean f
    _ = mean (fun f : Fin 4 → A => if f = (fun _ => a) then (1:ℚ) else 0) := by
          apply mean_congr
          intro f
          by_cases h : ∀ j : Fin 4, f j = a
          · have heq := (hu f).mp h
            simp [indicator, h, heq]
          · have hne : f ≠ (fun _ => a) := by
              intro heq
              exact h ((hu f).mpr heq)
            simp [indicator, h, hne]
    _ = 1 / (Fintype.card (Fin 4 → A) : ℚ) := mean_singleton (fun _ => a)
    _ = (1 / (Fintype.card A : ℚ)) ^ 4 := by
          have hc : Fintype.card (Fin 4 → A) = (Fintype.card A)^4 := by simp
          rw [hc, Nat.cast_pow]
          ring

theorem lowFourZero_mean :
    mean (fun f : Fin 4 → Fin modulus => indicator (∀ j, f j = z31)) =
      (1 / (modulus : ℚ)) ^ 4 := by
  classical
  haveI : Nonempty (Fin 4 → Fin modulus) := ⟨zeroFn4⟩
  have hu (f : Fin 4 → Fin modulus) : (∀ j, f j = z31) ↔ f = zeroFn4 := by
    constructor
    · intro h; funext j; exact h j
    · intro h j; simpa [zeroFn4] using congrFun h j
  calc
    mean (fun f : Fin 4 → Fin modulus => indicator (∀ j, f j = z31))
      = mean (fun f => if f = zeroFn4 then (1:ℚ) else 0) := by
        apply mean_congr
        intro f
        by_cases h : ∀ j, f j = z31
        · have heq := (hu f).mp h
          simp [indicator, h, heq, zeroFn4]
        · have hne : f ≠ zeroFn4 := by
            intro heq
            exact h ((hu f).mpr heq)
          simp [indicator, h, hne]
    _ = 1 / (Fintype.card (Fin 4 → Fin modulus) : ℚ) := mean_singleton zeroFn4
    _ = (1 / (modulus : ℚ)) ^ 4 := by
        have hc : Fintype.card (Fin 4 → Fin modulus) = modulus ^ 4 := by simp
        rw [hc, Nat.cast_pow]
        ring

theorem firstFourZero_mean :
    mean (fun block : State => indicator (firstFourZero block)) =
      (1 / (modulus : ℚ)) ^ 4 := by
  classical
  have hsource : mean (fun block : State => indicator (firstFourZero block)) =
      mean (fun block : State => indicator (firstFourListZero (words 31 block))) := by
    apply mean_congr
    intro block
    apply congrArg indicator
    apply propext
    rw [words31_value]
    constructor
    · intro h j
      rw [ofFn_at_four]
      have hm := h j
      rw [← masked31_value] at hm
      simp [hm]
    · intro h j
      have hj := h j
      rw [ofFn_at_four] at hj
      simp only [Option.some.injEq] at hj
      rw [← masked31_value]
      simpa [z31] using hj
  rw [hsource]
  rw [uniform_masked31_block (fun xs => indicator (firstFourListZero xs))]
  haveI : Nonempty (Fin modulus) := ⟨z31⟩
  have hlistfield : mean (fun f : Fin 8 → Fin modulus =>
      indicator (firstFourListZero (List.ofFn (fun j => (f j).val)))) =
        mean (fun f : Fin 8 → Fin modulus => indicator (prefixFourEq z31 f)) := by
    apply mean_congr
    intro f
    apply congrArg indicator
    apply propext
    constructor
    · intro h j
      have hj := h j
      rw [ofFn_at_four] at hj
      simp only [Option.some.injEq] at hj
      exact Fin.ext (by simpa [z31] using hj)
    · intro h j
      rw [ofFn_at_four]
      have hj := h j
      have hv := congrArg Fin.val hj
      simpa [z31] using hv
  calc
    mean (fun f : Fin 8 → Fin modulus => indicator
      (firstFourListZero (List.ofFn (fun j => (f j).val))))
      = mean (fun f : Fin 8 → Fin modulus => indicator (prefixFourEq z31 f)) := hlistfield
    _ = (1 / (modulus : ℚ)) ^ 4 := by
      simpa only [Fintype.card_fin] using (prefixFour_mean (A := Fin modulus) z31)

#print axioms mean_singleton
#print axioms splitFin8Four
#print axioms ofFn_at_four
#print axioms prefixFour_mean
#print axioms lowFourZero_mean
#print axioms firstFourZero_mean
end
end AspisV8R19.R551FirstFourZeroBlockV10
