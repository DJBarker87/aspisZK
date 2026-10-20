import AeneasOriginalPolynomialBodyAdapterV1
import CurrentFinishCandidateUnrolledPolynomialV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.OriginalPolynomialFinishBridge

open AspisR1CurrentWide.Proof

abbrev FinishOps := AspisR1FinishRelationCurrent.FinishOps

def finishOriginalPolynomial (poly : Slice U8) (alpha : FinishE) : Result FinishE := do
  let out ← AspisR1CurrentWide.OriginalPolynomialBodyAdapter.originalEmittedPolynomialBody
    poly (ofFinishE alpha)
  ok (toFinishE out)

theorem finish_original_polynomial_eq_unrolled
    (poly : Slice U8) (alpha : FinishE) :
    finishOriginalPolynomial poly alpha = finishUnrolledPolynomial poly alpha := by
  unfold finishOriginalPolynomial finishUnrolledPolynomial
  rw [AspisR1CurrentWide.OriginalPolynomialBodyAdapter.originalEmittedPolynomialBody_eq_unrolled]

def finishOriginalPolynomialOps {W D : Type} (ops : FinishOps W D) : FinishOps W D :=
  { finishConcreteField ops with polynomial := finishOriginalPolynomial }

theorem finish_original_polynomial_ops_eq_unrolled {W D : Type}
    (ops : FinishOps W D) :
    finishOriginalPolynomialOps ops = finishUnrolledPolynomialOps ops := by
  change { finishConcreteField ops with polynomial := finishOriginalPolynomial } =
    { finishConcreteField ops with polynomial := finishUnrolledPolynomial }
  have hp : finishOriginalPolynomial = finishUnrolledPolynomial := by
    funext poly alpha
    exact finish_original_polynomial_eq_unrolled poly alpha
  rw [hp]

theorem finish_relation_original_ops_eq_unrolled {W D : Type}
    (ops : FinishOps W D) (v : AspisR1FinishRelationCurrent.verifier.View)
    (p : AspisR1FinishRelationCurrent.verifier.Prepared)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit)) :
    AspisR1FinishRelationCurrent.verifier.finish_relation
        (finishOriginalPolynomialOps ops) v p a obs =
      AspisR1FinishRelationCurrent.verifier.finish_relation
        (finishUnrolledPolynomialOps ops) v p a obs := by
  rw [finish_original_polynomial_ops_eq_unrolled]

theorem s2_original_polynomial_success_equations {W D : Type}
    (ops : FinishOps W D) (v : AspisR1FinishRelationCurrent.verifier.View)
    (p : AspisR1FinishRelationCurrent.verifier.Prepared)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hv : p.variant = AspisR1FinishRelationCurrent.transport.Variant.S2)
    (hclaim : CanonicalFinish p.claim)
    (halpha0 : ∀ x, Array.index_usize p.alpha 0#usize = .ok x → CanonicalFinish x)
    (halpha1 : ∀ x, Array.index_usize p.alpha 1#usize = .ok x → CanonicalFinish x)
    (h : AspisR1FinishRelationCurrent.verifier.finish_relation
      (finishOriginalPolynomialOps ops) v p a obs = .ok (.Ok ())) :
    ∃ alpha0 claim1 alpha1 claim2 w sliced pair actual,
      Array.index_usize p.alpha 0#usize = .ok alpha0 ∧
      CanonicalFinish claim1 ∧
      (∃ x0 x4, finishField v.round0 0#usize = .ok x0 ∧
        finishField v.round0 4#usize = .ok x4 ∧
        decodeFinish x0 + decodeFinish x4 = decodeFinish p.claim * (536870912 : AspisWideTower.WideExact)) ∧
      Array.index_usize p.alpha 1#usize = .ok alpha1 ∧
      CanonicalFinish claim2 ∧
      (∃ x0 x4, finishField v.round1 0#usize = .ok x0 ∧
        finishField v.round1 4#usize = .ok x4 ∧
        decodeFinish x0 + decodeFinish x4 = decodeFinish claim1 * (536870912 : AspisWideTower.WideExact)) ∧
      (finishOriginalPolynomialOps ops).newWeights p.variant p.semantic_alpha p.z = .ok (.Ok w) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice AspisR1FinishRelationCurrent.aspis_core.field.WideExact))
        p.alpha { «end» := 2#usize } = .ok sliced ∧
      (finishOriginalPolynomialOps ops).pair w sliced v.final_message p.kappa = .ok (.Ok pair) ∧
      pair = claim2 ∧
      AspisR1FinishRelationCurrent.verifier.finish_query_dot (finishOriginalPolynomialOps ops)
        v.final_message (alloc.vec.Vec.deref a.weights) = .ok (.Ok actual) ∧
      actual = a.rhs ∧ a.next = 22#usize := by
  have h' : AspisR1FinishRelationCurrent.verifier.finish_relation
      (finishUnrolledPolynomialOps ops) v p a obs = .ok (.Ok ()) := by
    rw [← finish_relation_original_ops_eq_unrolled]
    exact h
  simpa only [finish_original_polynomial_ops_eq_unrolled] using
    (s2_unrolled_polynomial_success_equations ops v p a obs hv hclaim
      halpha0 halpha1 h')

#print axioms finish_original_polynomial_eq_unrolled
#print axioms finish_relation_original_ops_eq_unrolled
#print axioms s2_original_polynomial_success_equations

end AspisR1CurrentWide.OriginalPolynomialFinishBridge
