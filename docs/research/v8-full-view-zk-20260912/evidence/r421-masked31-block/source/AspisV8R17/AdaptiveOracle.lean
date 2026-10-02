import AspisV8Privacy.FiniteGames
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite

/-! Deferred decisions for a finite shared oracle and a causal query policy.
The policy sees the previous address/answer log, not unread oracle cells.
This is not yet a refinement of the source transcript/commitment machine. -/
set_option autoImplicit false
namespace AspisV8R17.AdaptiveOracle
variable {I A : Type*} [DecidableEq I]

def run (next : List (I × A) → I) (H : I → A) : ℕ → List (I × A) → List (I × A)
  | 0, _ => []
  | n+1, history =>
    let i := next history
    (i,H i) :: run next H n (history ++ [(i,H i)])

omit [DecidableEq I] in
theorem run_congr_on_reads (next : List (I × A) → I) (H G : I → A)
    (n : ℕ) (history : List (I × A))
    (agrees : ∀ p ∈ run next H n history, G p.1 = H p.1) :
    run next G n history = run next H n history := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
    have hh : G (next history) = H (next history) :=
      agrees (next history, H (next history)) (by simp [run])
    simp only [run, hh]
    congr 1
    apply ih
    intro p hp
    exact agrees p (by simp [run, hp])

theorem unread_update_preserves_trace (next : List (I × A) → I) (H : I → A)
    (n : ℕ) (history : List (I × A)) (i : I) (a : A)
    (unread : ∀ p ∈ run next H n history, p.1 ≠ i) :
    run next (Function.update H i a) n history = run next H n history := by
  apply run_congr_on_reads
  intro p hp
  exact Function.update_of_ne (unread p hp) a H

def cellEquiv (i : I) (e : A ≃ A) : (I → A) ≃ (I → A) where
  toFun H := Function.update H i (e (H i))
  invFun H := Function.update H i (e.symm (H i))
  left_inv H := by funext j; by_cases h : j=i <;> simp [h, Function.update_of_ne]
  right_inv H := by funext j; by_cases h : j=i <;> simp [h, Function.update_of_ne]

def traceCellFiberEquiv (next : List (I × A) → I) (n : ℕ)
    (tr : List (I × A)) (i : I) (unread : ∀ p ∈ tr, p.1 ≠ i)
    (e : A ≃ A) (a : A) :
    {H : I → A // run next H n [] = tr ∧ H i = a} ≃
    {H : I → A // run next H n [] = tr ∧ H i = e a} where
  toFun H := ⟨cellEquiv i e H.val, by
    constructor
    · exact (unread_update_preserves_trace next H.val n [] i _
        (by simpa [H.property.1] using unread)).trans H.property.1
    · simp [cellEquiv, H.property.2]⟩
  invFun H := ⟨(cellEquiv i e).symm H.val, by
    constructor
    · exact (unread_update_preserves_trace next H.val n [] i _
        (by simpa [H.property.1] using unread)).trans H.property.1
    · simp [cellEquiv, H.property.2]⟩
  left_inv H := by apply Subtype.ext; exact (cellEquiv i e).symm_apply_apply H.val
  right_inv H := by apply Subtype.ext; exact (cellEquiv i e).apply_symm_apply H.val

theorem fresh_cell_counts_equal [Fintype I] [Fintype A] [DecidableEq A]
    (next : List (I × A) → I) (n : ℕ) (tr : List (I × A))
    (i : I) (unread : ∀ p ∈ tr, p.1 ≠ i) (a b : A) :
    AspisV8Privacy.fiberCount (fun H : I → A => (run next H n [], H i)) (tr,a) =
      AspisV8Privacy.fiberCount (fun H : I → A => (run next H n [], H i)) (tr,b) := by
  classical
  unfold AspisV8Privacy.fiberCount
  simp only [Fintype.card_eq_nat_card]
  let left : {H : I → A // (run next H n [], H i) = (tr,a)} ≃
      {H : I → A // run next H n [] = tr ∧ H i = a} :=
    Equiv.subtypeEquivRight (fun _ => by simp only [Prod.mk.injEq])
  let right : {H : I → A // (run next H n [], H i) = (tr,b)} ≃
      {H : I → A // run next H n [] = tr ∧ H i = b} :=
    Equiv.subtypeEquivRight (fun _ => by simp only [Prod.mk.injEq])
  apply Nat.card_congr
  exact left.trans ((traceCellFiberEquiv next n tr i unread (Equiv.swap a b) a).trans
    ((Equiv.subtypeEquivRight (fun _ => by simp)).trans right.symm))

theorem fresh_next_joint_probabilities [Fintype I] [Fintype A] [Nonempty A]
    [DecidableEq A] (next : List (I × A) → I) (n : ℕ) (tr : List (I × A))
    (unread : ∀ p ∈ tr, p.1 ≠ next tr) (a b : A) :
    AspisV8Privacy.uniformProbability
      (fun H : I → A => (run next H n [], H (next tr))) (tr,a) =
    AspisV8Privacy.uniformProbability
      (fun H : I → A => (run next H n [], H (next tr))) (tr,b) := by
  unfold AspisV8Privacy.uniformProbability
  rw [fresh_cell_counts_equal next n tr (next tr) unread a b]

#print axioms fresh_next_joint_probabilities
#print axioms run_congr_on_reads
#print axioms unread_update_preserves_trace
#print axioms cellEquiv
#print axioms traceCellFiberEquiv
#print axioms fresh_cell_counts_equal
end AspisV8R17.AdaptiveOracle
