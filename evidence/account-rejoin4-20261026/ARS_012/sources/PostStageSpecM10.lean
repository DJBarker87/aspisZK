import AbstractStageSpecM10
import GSPostProcessCompleteM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.PostStageSpecM10
open AspisWideTower GSFixedInputDecoderFamily AbstractStageSpecM10 GSPostProcessWorkM10
open AspisPool.AlgorithmicCircleDecoderV7
attribute [local irreducible] GSPostProcessCompleteM10.eval GSPostProcessCompleteM10.budget
  LiteralComputedCandidateExtract.extract GSByteJointSpendExtractor.decodedLists

@[irreducible] def spec (image : PublicImage) (C : Nat) (hi : PublicImageBound image C)
    (pub : R0P.Public AspisV8R15.ExactTowerBase.M31Exact)
    (W : Fin 29 → InitialWord WideExact) :
    StageSpec (fun out : Results WideExact 5 => LiteralComputedCandidateExtract.extract pub W
        (GSByteJointSpendExtractor.decodedLists W out))
      (fun out => GSBankOutputEnvelopeM10.Bounded out ∧ pub.nextPairIndex < 2^64) (fun _ => True) (fun _ => GSPostProcessCompleteM10.budget C) where
  run := GSPostProcessCompleteM10.eval image pub W
  value := GSPostProcessCompleteM10.value image pub W
  work _ out ho := GSPostProcessCompleteM10.work image C hi pub ho.2 W out ho.1
  invariant _ _ _ _ := True.intro

theorem value (image : PublicImage) (C : Nat) (hi : PublicImageBound image C)
    (pub : R0P.Public AspisV8R15.ExactTowerBase.M31Exact)
    (W : Fin 29 → InitialWord WideExact) (out : Results WideExact 5) :
    ((spec image C hi pub W).run out).1 = LiteralComputedCandidateExtract.extract pub W
        (GSByteJointSpendExtractor.decodedLists W out) := (spec image C hi pub W).value out

#print axioms value
end AspisR1.PostStageSpecM10
end
