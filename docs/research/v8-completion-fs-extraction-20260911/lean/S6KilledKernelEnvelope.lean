import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! FIRST-ATTEMPT universal finite-kernel proof.
A fresh-output transition samples a block with nonnegative weights. Its
advance/continuation kernel may depend on the block and may lose mass. At a
cached output the analysis process is killed. The ideal envelope ignores
advance state. This is NOT the source-to-kernel refinement: that producer is
specified in design/KERNEL_PROOF.md and must be constructed separately.
-/
set_option autoImplicit false
open scoped BigOperators
namespace AspisS6.KilledKernel
universe u v w x
variable {B : Type u} {S : Type v} {D : Type w} {A : Type x}
variable [Fintype B] [DecidableEq A]

inductive Step (D : Type w) (A : Type x) where
  | reject
  | finish (value : A)
  | more (state : D)

def score (future : D → ℚ) (target : A) : Step D A → ℚ
  | .reject => 0
  | .finish value => if value = target then 1 else 0
  | .more state => future state

def ideal (weights : B → ℚ) (decode : D → B → Step D A)
    (target : A) : Nat → D → ℚ
  | 0, _ => 0
  | n+1, state => ∑ b, weights b * score (ideal weights decode target n)
      target (decode state b)

def actual (weights : B → ℚ) (decode : D → B → Step D A)
    (fresh : S → Bool) (support : S → B → Finset S)
    (advance : S → B → S → ℚ) (target : A) : Nat → S → D → ℚ
  | 0, _, _ => 0
  | n+1, oracle, state =>
      if fresh oracle then
        ∑ b, weights b * ∑ next ∈ support oracle b,
          advance oracle b next *
            score (fun d => actual weights decode fresh support advance target n next d)
              target (decode state b)
      else 0

 theorem weighted_subkernel_le
    (support : Finset S) (weight value : S → ℚ) (cap : ℚ)
    (positive : ∀ s ∈ support, 0 ≤ weight s)
    (mass : ∑ s ∈ support, weight s ≤ 1)
    (capNonnegative : 0 ≤ cap)
    (bounded : ∀ s ∈ support, value s ≤ cap) :
    (∑ s ∈ support, weight s * value s) ≤ cap := by
  calc
    (∑ s ∈ support, weight s * value s)
        ≤ ∑ s ∈ support, weight s * cap := by
            apply Finset.sum_le_sum
            intro s hs
            exact mul_le_mul_of_nonneg_left (bounded s hs) (positive s hs)
    _ = (∑ s ∈ support, weight s) * cap := by rw [Finset.sum_mul]
    _ ≤ 1 * cap := mul_le_mul_of_nonneg_right mass capNonnegative
    _ = cap := one_mul cap

 theorem score_nonnegative (future : D → ℚ) (target : A)
    (next : Step D A) (positive : ∀ d, 0 ≤ future d) :
    0 ≤ score future target next := by
  cases next with
  | reject => exact le_rfl
  | finish value =>
      by_cases h : value = target <;> simp [score, h]
  | more state => exact positive state

 theorem ideal_nonnegative (weights : B → ℚ)
    (decode : D → B → Step D A) (target : A)
    (positive : ∀ b, 0 ≤ weights b) :
    ∀ n d, 0 ≤ ideal weights decode target n d := by
  intro n
  induction n with
  | zero => intro d; exact le_rfl
  | succ n ih =>
      intro d
      apply Finset.sum_nonneg
      intro b _
      exact mul_nonneg (positive b)
        (score_nonnegative _ target (decode d b) ih)

 theorem score_mono (left right : D → ℚ) (target : A)
    (next : Step D A) (bounded : ∀ d, left d ≤ right d) :
    score left target next ≤ score right target next := by
  cases next with
  | reject => exact le_rfl
  | finish value => exact le_rfl
  | more state => exact bounded state

/-- No independence or purity of the ADVANCE kernel is required beyond its
being a subprobability kernel. It may depend on the output block and include
cached values, resource failure and state-dependent continuation. -/
 theorem actual_le_ideal
    (weights : B → ℚ) (decode : D → B → Step D A)
    (fresh : S → Bool) (support : S → B → Finset S)
    (advance : S → B → S → ℚ) (target : A)
    (outputPositive : ∀ b, 0 ≤ weights b)
    (advancePositive : ∀ s b next, next ∈ support s b → 0 ≤ advance s b next)
    (advanceMass : ∀ s b, ∑ next ∈ support s b, advance s b next ≤ 1) :
    ∀ n s d,
      actual weights decode fresh support advance target n s d ≤
        ideal weights decode target n d := by
  intro n
  induction n with
  | zero => intro s d; exact le_rfl
  | succ n ih =>
      intro s d
      unfold actual
      split
      · apply Finset.sum_le_sum
        intro b _
        apply mul_le_mul_of_nonneg_left _ (outputPositive b)
        apply weighted_subkernel_le
          (support s b) (advance s b)
          (fun next => score
            (fun d' => actual weights decode fresh support advance target n next d')
            target (decode d b))
          (score (ideal weights decode target n) target (decode d b))
        · intro next member
          exact advancePositive s b next member
        · exact advanceMass s b
        · exact score_nonnegative _ target (decode d b)
            (ideal_nonnegative weights decode target outputPositive n)
        · intro next _
          exact score_mono _ _ target (decode d b) (ih next)
      · exact ideal_nonnegative weights decode target outputPositive (n+1) d

#print axioms weighted_subkernel_le
#print axioms ideal_nonnegative
#print axioms actual_le_ideal
end AspisS6.KilledKernel
