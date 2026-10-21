import R1Z.SimCostLazyCoupling
import R1Z.SimCostTruncationBudget

/-! Source-level finite rejection sampling. Uniform independent finite words
are explicit product coordinates, not an assumed geometric rejection law.
The result certifies residue codes; transport to the full simulator's field
tape and its total sample count remains a separate implementation obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostBinarySource
open R0Z R0Z.FsAbortBounds R1Z.SimCostWriter R1Z.SimCostSampling
  R1Z.SimCostLazyCoupling
attribute [local instance] Classical.propDecidable

/-- Consume at most B trials, with an explicit failure output. -/
def trials {A : Type} : (B : Nat) → (Fin B → Option A) → Costed (Option A)
  | 0, _ => (none,0)
  | B+1, u => match u (Fin.last B) with
    | some a => (some a,1)
    | none => let r := trials B (Fin.init u); (r.1,r.2+1)

theorem trials_bound {A : Type} (B : Nat) (u : Fin B → Option A) :
    (trials B u).2 ≤ B := by
  induction B with
  | zero => simp only [trials, le_refl]
  | succ B ih =>
    cases he : u (Fin.last B) with
    | none => simpa only [trials, he] using Nat.add_le_add_right (ih (Fin.init u)) 1
    | some a => simp only [trials, he]; omega

def rejection (A : Type) [Fintype A] : ℚ := 1 / (Fintype.card A + 1 : ℚ)

theorem option_mean {A : Type} [Fintype A] [Nonempty A] (f : Option A → ℚ) :
    mean f = rejection A * f none + (1-rejection A) * mean (fun a : A => f (some a)) := by
  unfold mean rejection
  rw [Fintype.sum_option, Fintype.card_option, Nat.cast_add, Nat.cast_one]
  have ha : (Fintype.card A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Fintype.card A : ℚ)+1 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact success-uniform / failure mixture for an actual independent source. -/
theorem trials_law {A : Type} [Fintype A] [Nonempty A] (B : Nat) (f : Option A → ℚ) :
    mean (fun u : Fin B → Option A => f (trials B u).1) =
      (rejection A)^B * f none + (1-(rejection A)^B) * mean (fun a : A => f (some a)) := by
  induction B with
  | zero => simp only [trials, mean_const', pow_zero, one_mul, sub_self, zero_mul, add_zero]
  | succ B ih =>
    rw [mean_snoc B, option_mean]
    simp only [Fin.snoc_last, Fin.init_snoc, trials, mean_const']
    rw [ih, pow_succ]
    ring

/-- The largest word is rejected; every other word is its own residue code. -/
def wordEquiv (m : Nat) : Fin (m+1) ≃ Option (Fin m) := finSuccEquiv' (Fin.last m)

theorem word_reject (m : Nat) : wordEquiv m (Fin.last m) = none :=
  finSuccEquiv'_at _

def streamEquiv (m B : Nat) : (Fin B → Fin (m+1)) ≃ (Fin B → Option (Fin m)) where
  toFun u i := wordEquiv m (u i)
  invFun u i := (wordEquiv m).symm (u i)
  left_inv u := by funext i; exact (wordEquiv m).symm_apply_apply _
  right_inv u := by funext i; exact (wordEquiv m).apply_symm_apply _

def words (m B : Nat) (u : Fin B → Fin (m+1)) : Costed (Option (Fin m)) :=
  trials B (streamEquiv m B u)

theorem words_law (m : Nat) [NeZero m] (B : Nat) (f : Option (Fin m) → ℚ) :
    mean (fun u : Fin B → Fin (m+1) => f (words m B u).1) =
      (rejection (Fin m))^B * f none +
        (1-(rejection (Fin m))^B) * mean (fun a : Fin m => f (some a)) := by
  have he := mean_equiv' (streamEquiv m B)
    (fun u : Fin B → Fin (m+1) => f (words m B u).1)
  have hs : (fun u : Fin B → Option (Fin m) => f (words m B ((streamEquiv m B).symm u)).1) =
      (fun u => f (trials B u).1) := by
    funext u
    unfold words
    rw [Equiv.apply_symm_apply]
  rw [hs] at he
  exact he.trans (trials_law B f)

/-- Explicit uniform 31-bit input words. The all-ones value 2^31-1 is
rejected, and accepted codes are exactly Fin (2^31-1), uniformly distributed. -/
theorem m31_source_law (B : Nat) (f : Option (Fin 2147483647) → ℚ) :
    mean (fun u : Fin B → Fin 2147483648 => f (words 2147483647 B u).1) =
      m31Reject^B * f none + (1-m31Reject^B) * mean (fun a : Fin 2147483647 => f (some a)) := by
  have hr : rejection (Fin 2147483647) = m31Reject := by
    norm_num [rejection, m31Reject, Fintype.card_fin]
  simpa only [hr] using words_law 2147483647 B f

/-- Exact truncation failure mass, proved from the uniform binary-word source. -/
theorem m31_source_tail (B : Nat) :
    mean (fun u : Fin B → Fin 2147483648 =>
      if (words 2147483647 B u).1 = none then (1:ℚ) else 0) = 1/(2:ℚ)^(31*B) := by
  have hh := m31_source_law B (fun value => if value = none then (1:ℚ) else 0)
  simpa only [Option.some_ne_none, if_false, if_true, mean_const', mul_one, mul_zero,
    add_zero, m31_tail] using hh

#print axioms trials_bound
#print axioms option_mean
#print axioms trials_law
#print axioms word_reject
#print axioms words_law
#print axioms m31_source_law
#print axioms m31_source_tail
end R1Z.SimCostBinarySource
