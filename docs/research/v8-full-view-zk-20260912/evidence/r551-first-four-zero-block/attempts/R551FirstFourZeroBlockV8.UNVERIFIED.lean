import AspisV8R19.R421UniformMasked31Block
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R551FirstFourZeroBlockV8
open DuplexFrames SourceDuplexStep SamplerWords OracleResampling
open R421UniformMasked31Block
noncomputable section
def modulus : Nat := 2^31
noncomputable def indicator (p : Prop) : ℚ := by classical exact if p then 1 else 0
def z31 : Fin modulus := ⟨0, by norm_num [modulus]⟩
def zeroFn4 : Fin 4 → Fin modulus := fun _ => z31
def firstFourZero (block : State) : Prop := ∀ j : Fin 4, masked 31 (word block ⟨j.val, by omega⟩) = 0
def lowFourZero (f : Fin 4 → Fin modulus) : Prop := ∀ j, f j = z31
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

theorem lowFourZero_mean : mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) =
    (1 / (modulus : ℚ)) ^ 4 := by
  classical
  haveI : Nonempty (Fin 4 → Fin modulus) := ⟨zeroFn4⟩
  have hu (f : Fin 4 → Fin modulus) : lowFourZero f ↔ f = zeroFn4 := by
    constructor
    · intro h; funext j; exact h j
    · intro h j; simpa [zeroFn4] using congrFun h j
  calc
    mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f))
        = mean (fun f => if f = zeroFn4 then (1:ℚ) else 0) := by
            apply mean_congr
            intro f
            simp only [indicator]
            simp [hu f]
    _ = 1 / (Fintype.card (Fin 4 → Fin modulus) : ℚ) := mean_singleton zeroFn4
    _ = (1 / (modulus : ℚ)) ^ 4 := by
      have hc : Fintype.card (Fin 4 → Fin modulus) = modulus ^ 4 := by simp
      rw [hc, Nat.cast_pow]
      ring

theorem firstFourZero_mean :
    mean (fun block : State => indicator (firstFourZero block)) = (1 / (modulus : ℚ)) ^ 4 := by
  classical
  have hsource : mean (fun block : State => indicator (firstFourZero block)) =
      mean (fun block : State => indicator (firstFourListZero (words 31 block))) := by
    apply mean_congr
    intro block
    apply congrArg indicator
    apply propext
    rw [words31_value]
    change (∀ j : Fin 4, masked 31 (word block ⟨j.val, by omega⟩) = 0) ↔
      (∀ j : Fin 4, (List.ofFn (fun k : Fin 8 => ((splitBlock31Equiv block).2 k).val))[j.val]? = some 0)
    constructor
    · intro h j
      fin_cases j <;> simp [List.getElem?_ofFn, masked31_value, z31, h]
    · intro h j
      have hj := h j
      fin_cases j <;> simp_all [List.getElem?_ofFn, masked31_value, z31]
  rw [hsource]
  rw [uniform_masked31_block (fun xs => indicator (firstFourListZero xs))]
  have hfield : mean (fun f : Fin 8 → Fin modulus => indicator
      (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31)) = (1 / (modulus : ℚ)) ^ 4 := by
    calc
      _ = mean (fun p : (Fin 4 → Fin modulus) × (Fin 4 → Fin modulus) =>
          indicator (lowFourZero p.1)) := by
            calc
              _ = mean (fun f : Fin 8 → Fin modulus => indicator (lowFourZero (splitFin8Four f).1)) := by
                apply mean_congr
                intro f
                apply congrArg indicator
                apply propext
                rfl
              _ = _ := mean_equiv (splitFin8Four (A := Fin modulus)) _
      _ = mean (fun f : Fin 4 → Fin modulus => indicator (lowFourZero f)) := by
            haveI : Nonempty (Fin 4 → Fin modulus) := ⟨zeroFn4⟩
            calc
              _ = mean (fun f : Fin 4 → Fin modulus =>
                    mean (fun _ : Fin 4 → Fin modulus => indicator (lowFourZero f))) :=
                    mean_prod (fun f _ => indicator (lowFourZero f))
              _ = _ := by
                    apply mean_congr
                    intro f
                    rw [mean_const]
      _ = _ := lowFourZero_mean
  have hlistfield : mean (fun f : Fin 8 → Fin modulus =>
      indicator (firstFourListZero (List.ofFn (fun j => (f j).val)))) =
        mean (fun f : Fin 8 → Fin modulus => indicator
          (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31)) := by
      apply mean_congr
      intro f
      apply congrArg indicator
      apply propext
      change (∀ j : Fin 4, (List.ofFn (fun k : Fin 8 => (f k).val))[j.val]? = some 0) ↔
        (∀ j : Fin 4, f ⟨j.val, by omega⟩ = z31)
      constructor
      · intro h j
        fin_cases j <;> simp_all [List.getElem?_ofFn, z31]
      · intro h j
        fin_cases j <;> simp_all [List.getElem?_ofFn, z31]
  rw [hlistfield, hfield]

#print axioms mean_singleton
#print axioms splitFin8Four
#print axioms lowFourZero_mean
#print axioms firstFourZero_mean
end
end AspisV8R19.R551FirstFourZeroBlockV8
