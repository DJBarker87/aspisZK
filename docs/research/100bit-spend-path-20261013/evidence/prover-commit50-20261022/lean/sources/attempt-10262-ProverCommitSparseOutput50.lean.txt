import R1Z.ProverCommitSparseSum50
/-! Full prefix enumeration and exact finite-sum value, without an assumed
result image. Count input is a public encoding of 2^width. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSparseOutput50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open scoped BigOperators

theorem total_fin (p col : Nat → Old.Q) (w t s n o : Nat) :
    ProverCommitSparseSum50.total p col w t s n o=
      ∑ i : Fin n, ProverCommitSparseSum50.term p col w t s (o+i.val) := by
  induction n generalizing o with
  | zero => simp only [ProverCommitSparseSum50.total,Fin.sum_univ_zero]
  | succ n ih =>
    rw [ProverCommitSparseSum50.total,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem exact_result (p col : Nat → Old.Q)
    (hp : ∀ i, i<10 → Canonical (p i)) (hc : ∀ j, j<1024 → Canonical (col j))
    (width trailing : U8) (hwidth : width.val+trailing.val=10)
    (suffix : Usize) (hs : suffix.val<2^trailing.val)
    (count : U16) (hcount : count.val=2^width.val) :
    ∃ z : Old.Q, sparse_sum50.sum (ProverCommitQArray48.array 10#usize p)
      (ProverCommitQArray48.array 1024#usize col) width trailing suffix 0#usize count
      (ProverCommitNativeQ48.source zero)=ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=∑ a : Fin (2^width.val),
        ProverCommitSparseSum50.weight (fun i => decode (p i)) width.val a.val*
          decode (col (a.val*2^trailing.val+suffix.val)) := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitSparseSum50.sum p col hp hc width trailing hwidth suffix
    0#usize hs (2^width.val) count hcount (by change 0+2^width.val≤2^width.val;omega) zero zero_canonical
  refine ⟨z,hz,hcz,?_⟩
  rw [hdz,zero_decode,zero_add,total_fin]
  simp only [show (0#usize).val=0 from rfl,Nat.zero_add,ProverCommitSparseSum50.term]

#print axioms total_fin
#print axioms exact_result
end R1Z.ProverCommitSparseOutput50
