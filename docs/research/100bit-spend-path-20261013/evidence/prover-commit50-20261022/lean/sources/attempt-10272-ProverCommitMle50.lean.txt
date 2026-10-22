import R1Z.ProverCommitSparseParams50
import R1Z.ProverCommitSparseOutput50
import R1Z.ProverCommitSparseDense50
import R1Z.ProverCommitSparseRows50
/-! Complete owned sparse MLE caller. Every prefix/suffix/count/weight value
comes from a proved producer. Only canonical point/column inputs remain. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMle50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open scoped BigOperators
attribute [local irreducible] ProverCommitSparseDense50.dense ProverCommitSparseDense50.sparse

theorem exact_result (p col : Nat → Old.Q)
    (hp : ∀ i, i<10 → Canonical (p i)) (hc : ∀ j, j<1024 → Canonical (col j)) :
    ∃ z : Old.Q, mle50.mle (ProverCommitQArray48.array 10#usize p) (ProverCommitQArray48.array 1024#usize col)=
      ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=ProverCommitSparseDense50.dense (fun i => decode (p i)) (fun j => decode (col j)) 10 := by
  obtain ⟨width,trailing,suffix,hw,ht,hs,hwidth,hsb,hpoint⟩ := ProverCommitSparseParams50.parameters p hp
  obtain ⟨count,hcount,hcv⟩ := ProverCommitSparseParams50.count width (by omega)
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitSparseOutput50.exact_result p col hp hc width trailing hwidth
    suffix hsb count hcv
  refine ⟨z,?_,hcz,?_⟩
  · rw [mle50.mle,hw]
    simp only [bind_tc_ok,lift]
    rw [←ht,hs]
    simp only [bind_tc_ok,hcount,ProverCommitQArray48.source_zero]
    exact hz
  · have hdense := ProverCommitSparseDense50.dense_sparse (fun i => decode (p i)) (fun j => decode (col j))
      width.val trailing.val (⟨suffix.val,hsb⟩ : Fin (2^trailing.val)) hpoint
    rw [hwidth] at hdense
    rw [hdense]
    simpa only [ProverCommitSparseDense50.sparse,ProverCommitSparseSum50.weight,
      ProverCommitSparse50.weight,ProverCommitBooleanEnum49.tail] using hdz

theorem dense_dot (p col : Nat → QM31Exact) :
    ProverCommitSparseDense50.dense p col 10=
      AspisR0.RoundNormalization.dot
        (AspisR0.Opening.eqWeight (R0P.SemSource.toR0 (fun i : Fin 10 => p i.val)))
        (fun j : Fin 1024 => col j.val) := by
  classical
  unfold ProverCommitSparseDense50.dense AspisR0.RoundNormalization.dot
  apply Finset.sum_congr rfl
  intro j hj
  rw [ProverCommitSparseRows50.row]

theorem model_result (p col : Nat → Old.Q)
    (hp : ∀ i, i<10 → Canonical (p i)) (hc : ∀ j, j<1024 → Canonical (col j)) :
    ∃ z : Old.Q, mle50.mle (ProverCommitQArray48.array 10#usize p) (ProverCommitQArray48.array 1024#usize col)=
      ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=AspisR0.RoundNormalization.dot
        (AspisR0.Opening.eqWeight (R0P.SemSource.toR0 (fun i : Fin 10 => decode (p i.val))))
        (fun j : Fin 1024 => decode (col j.val)) := by
  obtain ⟨z,hz,hcz,hdz⟩ := exact_result p col hp hc
  exact ⟨z,hz,hcz,hdz.trans (dense_dot _ _)⟩

#print axioms exact_result
#print axioms dense_dot
#print axioms model_result
end R1Z.ProverCommitMle50
