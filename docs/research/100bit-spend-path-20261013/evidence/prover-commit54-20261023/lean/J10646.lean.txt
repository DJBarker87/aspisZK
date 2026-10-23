import AspisR1ProducerRelease47.EncoderComplete54
import R1Z.ProverCommitEncoderLine54
import R1Z.ProverCommitEncoderLeaf54
import R1Z.ProverCommitEncoderPhiModel53
/-! Complete owned eval_at with derived geometry, and the common arithmetic
bridge from the recurrence to the final encoder. Native caller binding is separate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderExact54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitEncoderEval54
open ProverCommitEncoderMath54 AspisCircleTensorBinding AspisCircleGroupOrder

attribute [local irreducible] source value sourceArray eval ProverCommitEncoderMath54.evaluate doubledFactor naturalLineValue

theorem recurrence_value (f : Nat → Exact) (p : Nat → U32) (u : Fin 262144)
    (hp : ∀ k, k<8 → value (base (p k))=doubledFactor
      (algebraMap (ZMod P) Exact (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) k) :
    eval 8 f (fun i => value (base (p i))) 0=
      AspisWide.FinalEncoder.exactFinalEncoder (fun i => f i.val) u := by
  rw [wide_evaluate,nodes_congr 8 f (fun i => value (base (p i)))
    (doubledFactor (algebraMap (ZMod P) Exact (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)))
    0 (by intro k hk;simpa only [Nat.zero_add] using hp k hk),evaluate_natural,doubledFactor]
  rw [AspisWide.FinalEncoder.exactFinalEncoder,AspisWide.FinalEncoder.exactFinalLinear_apply,
    AspisV5FriConcreteEncoderApplicability.naturalCoefficientPolynomial_eval_eq_sum (by decide)]
  exact (Fin.sum_univ_eq_sum_range (fun i => f i*naturalLineValue
    (algebraMap (ZMod P) Exact (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) i) 256).symm

theorem eval_at_result (f : Nat → Raw) (hf : ∀ i, i<256 → canonical (f i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ z : Raw, eval_at (Array.to_slice (sourceArray 256#usize f)) j 8#usize=ok (source z) ∧
      canonical z ∧ value z=AspisWide.FinalEncoder.exactFinalEncoder (fun i => value (f i.val)) u := by
  obtain ⟨p,z,hp,hz,hcz,hdz⟩ := ProverCommitEncoderLine54.final_value f hf j u hj
  refine ⟨z,?_,hcz,hdz⟩
  rw [eval_at,hp]
  exact hz

#print axioms recurrence_value
#print axioms eval_at_result
end R1Z.ProverCommitEncoderExact54
