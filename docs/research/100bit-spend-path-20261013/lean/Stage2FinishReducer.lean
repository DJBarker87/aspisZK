import Stage2ContinuationTypes
import BatchedWeightsActualReducer
import AspisR1BatchedActualReducerFinish
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.Stage2FinishReducer

/-- S8's remaining owner re-pin is explicit: the stage-2 opaque reducer is
identified with the already proved candidate-12 generated reducer. -/
theorem canonical_after_repin
    (reduce : U64 → Result AspisR1Stage2.aspis_core.field.M31)
    (repin_S8 : ∀ x, reduce x =
      AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x)
    (x : U64) :
    ∃ z, reduce x = ok z ∧ z.val = x.val % AspisV8R17.RawReducer.P ∧
      z.val < AspisV8R17.RawReducer.P := by
  rw [repin_S8]
  exact BatchedWeightsActualReducer.generated_wrapper_mod x

/-- Transfer a bounded raw-cell residue invariant to the stage-2 reducer's
returned canonical value. This is the arithmetic finish needed by S8's
64-coordinate finalization invariant, not a Vec-loop simulation. -/
theorem residue_after_repin
    (reduce : U64 → Result AspisR1Stage2.aspis_core.field.M31)
    (repin_S8 : ∀ x, reduce x =
      AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x)
    (x : U64) (sum : Nat) (residue : x.val % AspisV8R17.RawReducer.P = sum % AspisV8R17.RawReducer.P) :
    ∃ z, reduce x = ok z ∧ z.val = sum % AspisV8R17.RawReducer.P ∧
      z.val < AspisV8R17.RawReducer.P := by
  obtain ⟨z,hz,he,hl⟩ := canonical_after_repin reduce repin_S8 x
  exact ⟨z,hz,he.trans residue,hl⟩

theorem four_push_finish_after_repin
    (reduce : U64 → Result AspisR1Stage2.aspis_core.field.M31)
    (repin_S8 : ∀ x, reduce x =
      AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x) (terms : Usize) (raw a b c d : Nat)
    (hcounter : terms.val + 3 < 2 ^ UScalarTy.Usize.numBits)
    (hboundary : terms.val % 4 = 0) (hr : raw < 2 ^ 34)
    (ha : a ≤ (2 ^ 31 - 2) ^ 2) (hb : b ≤ (2 ^ 31 - 2) ^ 2)
    (hc : c ≤ (2 ^ 31 - 2) ^ 2) (hd : d ≤ (2 ^ 31 - 2) ^ 2) :
    ∃ terms1 terms2 terms3,
      UScalar.add terms (1#usize) = .ok terms1 ∧ terms1.val = terms.val + 1 ∧
      UScalar.add terms1 (1#usize) = .ok terms2 ∧ terms2.val = terms.val + 2 ∧
      UScalar.add terms2 (1#usize) = .ok terms3 ∧ terms3.val = terms.val + 3 ∧
      let r1 := AspisR1BatchedActualCounter.actualSourcePush terms raw a
      let r2 := AspisR1BatchedActualCounter.actualSourcePush terms1 r1 b
      let r3 := AspisR1BatchedActualCounter.actualSourcePush terms2 r2 c
      let r4 := AspisR1BatchedActualCounter.actualSourcePush terms3 r3 d
      ∃ hfinal : r4 < 2 ^ 64, ∃ z,
        reduce
            (UScalar.ofNatCore r4 hfinal) = .ok z ∧
          z.val = (raw + a + b + c + d) % AspisR1BatchedFoldSourceStep.modulus ∧
          z.val < AspisR1BatchedFoldSourceStep.modulus := by
  simpa only [repin_S8, BatchedWeightsActualReducer.generated_wrapper_eq_current] using
    AspisR1BatchedActualReducerFinish.actual_four_push_finish terms raw a b c d
      hcounter hboundary hr ha hb hc hd

#print axioms four_push_finish_after_repin

#print axioms canonical_after_repin
#print axioms residue_after_repin
#print axioms AspisR1BatchedActualReducerFinish.actual_four_push_finish
#print axioms BatchedWeightsActualReducer.generated_wrapper_mod
end AspisR1.Stage2FinishReducer
