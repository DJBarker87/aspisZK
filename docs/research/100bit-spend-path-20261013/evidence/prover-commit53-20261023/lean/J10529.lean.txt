import R1Z.ProverCommitGammaOutput53
import R1Z.Batched
import R1Z.ProverCommitCoefficientModel51
/-! Identify the complete gamma-batched coefficient array with batchR1. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitGammaModel53
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitGammaCell53
open scoped BigOperators

theorem batch_apply {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (pi : Fin 1024 ≃ Fin 1024) (ch : R0Z.HonestView.Challenges K)
    (t : R0P.Trace K) (j : Fin 1024) :
    R1Z.Batched.batchR1 pi ch t j=∑ l : Fin 29, ch.opening 0^l.val*R0P.SemSource.coeffsOf pi t l j := by
  simp only [R1Z.Batched.batchR1,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,LinearMap.proj_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rfl

theorem exact_result (c : Nat → Nat → Raw)
    (hc : ∀ l, l<29 → ∀ j, j<1024 → canonical (c l j))
    (x : Raw) (hx : canonical x) (t : R0P.Trace Exact)
    (hcoeff : ∀ l : Fin 29, ∀ j : Fin 1024,
      value (c l.val j.val)=R0P.SemSource.coeffsOf AspisR1.rowEquiv t l j)
    (ch : R0Z.HonestView.Challenges Exact) (hg : value x=ch.opening 0) :
    ∃ out : Nat → Raw, ProverCommitGammaOutput53.run (table c) (source x)=ok (sourceArray 1024#usize out) ∧
      (∀ j, j<1024 → canonical (out j)) ∧
      ∀ j : Fin 1024, value (out j.val)=R1Z.Batched.batchR1 AspisR1.rowEquiv ch t j := by
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitGammaOutput53.exact_result c hc x hx
  refine ⟨out,hout,hcout,?_⟩
  intro j
  rw [hdout j,batch_apply,hg]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hcoeff l j]

#print axioms batch_apply
#print axioms exact_result
end R1Z.ProverCommitGammaModel53
