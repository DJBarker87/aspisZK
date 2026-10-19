import GSConcreteSecondFoldByteBankProjectionGeneric
import GSConcreteReceivedWordInputs

set_option autoImplicit false

namespace AspisWide.GSConcreteSecondFoldByteBankFromWords

open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSConcreteReceivedWordInputs
open AspisWide.GSWideExactAgreementInputs
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSSecondFoldActualFinalProjection
open AspisWide.GSFinalMessageCandidateFilter
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open AspisR1.ConcreteProjection
open M31AcceptFiber
open AspisR1.SecondFoldSparseProjectionCore
open AspisR1.GSConcreteByteDecoderBank
open AspisR1.GSRejectingSamplerDecoderBank
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSDecoderTapeReindex
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1.SecondFoldMatched
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisWide.GSConcreteSecondFoldByteBankProjectionGeneric

/-- Instantiate the byte-bank projection theorem with the actual received-word
point arrays. The point equalities are supplied by `fromWords`, not premises. -/
theorem byte_bank_nonfailure_implies_second_fold_projection_from_words
    (W : Fin 29 → InitialWord WideExact)
    (V : FinalWord WideExact) (g : Fin 4 → SmallWord WideExact)
    (alpha : WideExact)
    (hgood : alpha ∉ AspisR1.SecondFoldMatched.secondBad g)
    (f : SmallMessage WideExact)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hvalid : ∀ i ∈ S, curveValue g alpha i = secondEncoder f i)
    (xs : RawCoins)
    (hnofail : ¬ AspisR1.GSConcreteByteDecoderBank.failed
      (AspisWide.GSConcreteReceivedWordInputs.fromWords W
        (Fin.cases V (fun s => repeatedWord (g s)))) xs) :
    ∃ raw : AspisR1.GSRejectingSamplerDecoderBank.FlatTape WideExact,
      M31RetryOutputFiber.actualWidePairSamplerTape 21377328 xs = some raw ∧
      ∃ out : Results WideExact 5,
        out = AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149
          (AspisWide.GSConcreteReceivedWordInputs.fromWords W
            (Fin.cases V (fun s => repeatedWord (g s))))
          (flatBank WideExact (1025*112) (256*112) 149 raw) ∧
        ∃ roots : Fin 5 → List (List WideExact),
          (∀ i : Fin 5, out.2 i = some (roots i)) ∧
          (∃ b : Fin 4 → SmallMessage WideExact,
            f = ∑ s : Fin 4, alpha ^ s.val • b s ∧
            (∀ s : Fin 4,
              b s ∈ projectFinalCandidates (filterCandidates (roots (Fin.succ s))) ∧
              AspisR1.sparseLift (b s) ∈ finalRuntimeCloseList
                (repeatedWord (g s)) (roots (Fin.succ s)))) := by
  let finalWords : Fin 5 → FinalWord WideExact :=
    Fin.cases V (fun s => repeatedWord (g s))
  let inputs : Inputs WideExact 5 := fromWords W finalWords
  have hpointsV : inputs.finalPoints 0 = finalNormalizedPoints V := by
    dsimp [inputs, finalWords]
    simpa only [Fin.cases_zero] using finalPoints_normalized W
      (Fin.cases V (fun s => repeatedWord (g s))) 0
  have hpointsG : ∀ s : Fin 4,
      inputs.finalPoints (Fin.succ s) =
        finalNormalizedPoints (repeatedWord (g s)) := by
    intro s
    dsimp [inputs, finalWords]
    simpa only [Fin.cases_succ] using finalPoints_normalized W
      (Fin.cases V (fun s => repeatedWord (g s))) (Fin.succ s)
  exact byte_bank_nonfailure_implies_second_fold_projection
    V g inputs hpointsV hpointsG alpha hgood f S hS hvalid xs hnofail

#print axioms byte_bank_nonfailure_implies_second_fold_projection_from_words

end AspisWide.GSConcreteSecondFoldByteBankFromWords
