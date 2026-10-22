import R1Z.ProverCommitSparseEnum50
/-! Dense equality-weight evaluation equals the exact sparse row sum whenever
the suffix point is Boolean. No maximality of the suffix is required. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSparseDense50
open ProverCommitBooleanEnum49 ProverCommitSparseConcat50
open scoped BigOperators
variable {K : Type} [Field K]

def dense (p col : Nat → K) (n : Nat) : K :=
  ∑ r : Fin (2^n), ProverCommitSparse50.weight (fun i : Fin n => p i.val) (tail n r)*col r.val

def sparse (p col : Nat → K) (m n suffix : Nat) : K :=
  ∑ a : Fin (2^m), ProverCommitSparse50.weight (fun i : Fin m => p i.val) (tail m a)*
    col (a.val*2^n+suffix)

theorem dense_sparse (p col : Nat → K) (m n : Nat) (suffix : Fin (2^n))
    (hs : ∀ j : Fin n, p (m+j.val)=if tail n suffix j then 1 else 0) :
    dense p col (m+n)=sparse p col m n suffix.val := by
  have hpoint : (fun i : Fin (m+n) => p i.val)=Fin.append (fun i : Fin m => p i.val)
      (fun j : Fin n => if tail n suffix j then (1:K) else 0) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left];rfl
    · rw [Fin.append_right];exact hs j
  unfold dense
  rw [hpoint,ProverCommitSparseEnum50.prune]
  rfl

#print axioms dense_sparse
end R1Z.ProverCommitSparseDense50
