import R1Z.ProverCommitCoefficients51
import R0P.SemView
/-! The complete owned coefficient permutation yields coeffsOf rowEquiv. -/
set_option autoImplicit false
namespace R1Z.ProverCommitCoefficientModel51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0P.SemSource

theorem row (j : Fin 1024) :
    (⟨AspisR1.rowNat j.val,AspisR1.rowNat_lt j.val⟩ : Fin 1024)=AspisR1.rowEquiv.symm j := by
  apply AspisR1.rowEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  exact AspisR1.rowNat_involutive j.val j.isLt

theorem exact_result (p : Nat → Old.Q) (hp : ∀ i, i<1024 → Canonical (p i))
    (t : R0P.Trace QM31Exact) (l : Fin 29)
    (ht : ∀ j : Fin 1024, decode (p j.val)=t l j) :
    ∃ q : Nat → Old.Q,
      coefficients51.eval (ProverCommitQArray48.array 1024#usize p)=ok (ProverCommitQArray48.array 1024#usize q) ∧
      (∀ k, k<1024 → Canonical (q k)) ∧
      ∀ j : Fin 1024, decode (q j.val)=coeffsOf AspisR1.rowEquiv t l j := by
  obtain ⟨q,hq,hcq,hdq⟩ := ProverCommitCoefficients51.exact_result p hp
  refine ⟨q,hq,hcq,?_⟩
  intro j
  rw [hdq j.val j.isLt]
  have h := ht (⟨AspisR1.rowNat j.val,AspisR1.rowNat_lt j.val⟩ : Fin 1024)
  rw [row] at h
  exact h

#print axioms row
#print axioms exact_result
end R1Z.ProverCommitCoefficientModel51
