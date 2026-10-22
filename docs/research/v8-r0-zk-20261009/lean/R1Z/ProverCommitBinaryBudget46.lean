import R1Z.ProverCommitBinaryInvariant46
/-! Symbolic bounds for source cursor/count arithmetic. The native per-group
check runs in the admitted 16-entry domain at each of the eighteen levels. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBinaryBudget46
open Aeneas Aeneas.Std ProverCommitBinaryGroup46 ProverCommitBinarySupport46
open ProverCommitBinaryInvariant46 ProverCommitTreeSupport46

theorem missing_length (xs : List U32) : (layer xs).2.length ≤ xs.length := by
  cases xs with
  | nil => simp only [layer,List.length_nil,Nat.le_refl]
  | cons a tail =>
    have h := missing_length (tail.drop ((group a tail.head?).consumed.val-1))
    have head : (group a tail.head?).sibling.toList.length≤1 := by
      cases (group a tail.head?).sibling <;> simp
    rw [layer]
    simp only [List.length_append,List.length_cons,List.length_drop] at *
    omega
termination_by xs.length
decreasing_by
  simp only [List.length_drop,List.length_cons];omega

theorem count_bound (n : Nat) (xs : List U32) : count n xs ≤ n*xs.length := by
  induction n generalizing xs with
  | zero => simp only [count,Nat.zero_mul,Nat.le_refl]
  | succ n ih =>
    have h := layer_count xs
    rw [count,h.1,h.2]
    calc
      (layer xs).2.length+count n (layer xs).1 ≤ xs.length+n*xs.length :=
        Nat.add_le_add (missing_length xs)
          ((ih (layer xs).1).trans (Nat.mul_le_mul_left n (layer_length xs)))
      _ = (n+1)*xs.length := by rw [Nat.add_mul];omega

def Valid (xs : List U32) : Prop :=
  xs.Pairwise (fun a b => a.val<b.val) ∧ xs.length≤16 ∧ ∀ a∈xs, a.val<2^18

theorem valid_layer (xs : List U32) (valid : Valid xs) : Valid (layer xs).1 := by
  refine ⟨layer_sorted xs valid.1,(layer_length xs).trans valid.2.1,?_⟩
  intro p hp
  obtain ⟨i,hi,he⟩ := (layer_support xs {i | i<2^18} valid.2.2).1 p hp
  change i<2^18 at hi
  omega

/-- The whole eighteen-level count stays below every native arithmetic cap;
this bound does not replace the tighter per-slot rejection guards. -/
theorem count_eighteen (xs : List U32) (length : xs.length≤16) : count 18 xs ≤ 288 := by
  have h := count_bound 18 xs
  omega

theorem bytes_eighteen (xs : List U32) (length : xs.length≤16) : 32*count 18 xs ≤ 9216 := by
  have h := count_eighteen xs length
  omega

#print axioms missing_length
#print axioms count_bound
#print axioms valid_layer
#print axioms count_eighteen
#print axioms bytes_eighteen
end R1Z.ProverCommitBinaryBudget46
