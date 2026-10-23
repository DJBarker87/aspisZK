import R1Z.ProverCommitEncoderLift54
import Wide.FinalEncoder
/-! Owned evaluation at actual derived nodes equals the exact final encoder. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderLine54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitEncoderEval54
open ProverCommitEncoderMath54 ProverCommitEncoderLift54
open AspisCircleTensorBinding AspisCircleGroupOrder

attribute [local irreducible] value source sourceArray eval ProverCommitEncoderMath54.evaluate doubledFactor naturalLineValue

theorem finite_value (h : Nat) (hh : h≤8) (height : Usize) (hheight : height.val=h)
    (f : Nat → Raw) (hf : ∀ i, i<2^h → canonical (f i))
    (c : Slice Source) (hc : c.val=List.ofFn (fun i : Fin (2^h) => source (f i.val)))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ p z, nodes54.nodes j=ok (nodes p) ∧
      encoder54.eval_rec c 0#usize height (nodes p)=ok (source z) ∧ canonical z ∧
      value z=∑ i ∈ Finset.range (2^h), value (f i)*naturalLineValue
        (algebraMap (ZMod P) Exact (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) i := by
  obtain ⟨p,hp,hcp,hdp⟩ := nodes_image j u hj
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitEncoderEval54.exact_result h hh height 0#usize hheight
    (by change 0+h≤9;omega) f hf c hc p hcp
  refine ⟨p,z,hp,hz,hcz,?_⟩
  rw [hdz,wide_evaluate,show (0#usize).val=0 from rfl]
  rw [nodes_congr h (fun i => value (f i)) (fun i => value (base (p i)))
    (doubledFactor (algebraMap (ZMod P) Exact (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)))
    0 (by intro k hk;simpa only [Nat.zero_add] using hdp k (by omega))]
  rw [evaluate_natural,doubledFactor]

theorem final_value (f : Nat → Raw) (hf : ∀ i, i<256 → canonical (f i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ p z, nodes54.nodes j=ok (nodes p) ∧
      encoder54.eval_rec (Array.to_slice (sourceArray 256#usize f)) 0#usize 8#usize (nodes p)=ok (source z) ∧
      canonical z ∧ value z=AspisWide.FinalEncoder.exactFinalEncoder (fun i => value (f i.val)) u := by
  obtain ⟨p,z,hp,hz,hcz,hdz⟩ := finite_value 8 (by decide) 8#usize rfl f hf
    (Array.to_slice (sourceArray 256#usize f)) (by
      have hs : (256#usize).val=2^8 := rfl
      change (sourceArray 256#usize f).val=_
      simp only [sourceArray,hs,Fin.val_cast]) j u hj
  refine ⟨p,z,hp,hz,hcz,?_⟩
  rw [hdz]
  change (∑ i ∈ Finset.range 256, value (f i)*naturalLineValue
      (algebraMap (ZMod P) Exact (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) i)=_
  rw [AspisWide.FinalEncoder.exactFinalEncoder,AspisWide.FinalEncoder.exactFinalLinear_apply,
    AspisV5FriConcreteEncoderApplicability.naturalCoefficientPolynomial_eval_eq_sum (by decide)]
  exact (Fin.sum_univ_eq_sum_range (fun i => value (f i)*naturalLineValue
    (algebraMap (ZMod P) Exact (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) i) 256).symm

#print axioms finite_value
#print axioms final_value
end R1Z.ProverCommitEncoderLine54
