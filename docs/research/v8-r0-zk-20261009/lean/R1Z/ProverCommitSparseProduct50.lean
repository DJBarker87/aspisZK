import R1Z.ProverCommitSparseWeight50
import R1Z.ProverCommitSparse50
import R1Z.ProverCommitBooleanEnum49
/-! Complete prefix helper equals the mathematical equality weight, with
only source-input canonicality, length, and prefix-range premises. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSparseProduct50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open scoped BigOperators

theorem product_fin (p : Nat → Old.Q) (pref : Usize) (w n o : Nat) :
    ProverCommitSparseWeight50.product p pref w n o=
      ∏ j : Fin n, ProverCommitSparseWeight50.factorValue p pref w (o+j.val) := by
  induction n generalizing o with
  | zero => simp only [ProverCommitSparseWeight50.product,Fin.prod_univ_zero]
  | succ n ih =>
    rw [ProverCommitSparseWeight50.product,ih,Fin.prod_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem full_weight (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (width : U8) (hw : width.val≤10) (pref : Usize) (hb : pref.val<2^width.val) :
    ∃ z : Old.Q, sparse50.weight (ProverCommitQArray48.array 10#usize p) pref width 0#usize width
      (ProverCommitNativeQ48.source ProverCommitSubtraction47.one)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=ProverCommitSparse50.weight
        (fun i : Fin width.val => decode (p i.val))
        (ProverCommitBooleanEnum49.tail width.val ⟨pref.val,hb⟩) := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitSparseWeight50.weight p hp pref width hw width.val
    0#usize width rfl (by change 0+width.val≤width.val;omega)
    ProverCommitSubtraction47.one ProverCommitSubtraction47.one_canonical
  refine ⟨z,hz,hcz,?_⟩
  rw [hdz,ProverCommitSubtraction47.one_decode,one_mul,product_fin]
  unfold ProverCommitSparse50.weight
  apply Finset.prod_congr rfl
  intro i hi
  simp only [show (0#usize).val=0 from rfl,Nat.zero_add]
  rw [ProverCommitSparseWeight50.factorValue,
    ProverCommitBooleanEnum49.bit_tail width.val ⟨pref.val,hb⟩ pref rfl i]

#print axioms product_fin
#print axioms full_weight
end R1Z.ProverCommitSparseProduct50
