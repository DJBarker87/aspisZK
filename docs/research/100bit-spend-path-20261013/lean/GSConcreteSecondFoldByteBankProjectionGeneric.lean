import GSConcreteByteDecoderBank
import GSRejectingSamplerDecoderBank
import M31PairedWideSamplerLaw
import M31AcceptFiber
import GSSecondFoldActualFinalProjection
import GSNonfailureFinalRootsGeneric

set_option autoImplicit false

namespace AspisWide.GSConcreteSecondFoldByteBankProjectionGeneric

open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSWideExactAgreementInputs
open AspisWide.GSSecondFoldActualFinalProjection
open AspisR1.ConcreteProjection
open M31AcceptFiber
open M31RetryOutputFiber
open AspisWide.GSFinalMessageCandidateFilter
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open AspisR1.SecondFoldSparseProjectionCore
open AspisR1.SecondFoldSparseProjectionBridge
open AspisR1.GSConcreteByteDecoderBank
open AspisR1.GSRejectingSamplerDecoderBank
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSDecoderTapeReindex
open AspisR1.SecondFoldMatched
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisV5FriDegreeThreeCorrelatedAgreement

attribute [local irreducible] AspisR1.GSFixedInputDecoderFamily.run
  AspisR1.GSConcreteRootRecovery.initial
  AspisR1.GSConcreteRootRecovery.final

/-- The actual byte-bank nonfailure event supplies the point equalities and
all five final successes needed by the second-fold projection theorem. -/
theorem byte_bank_nonfailure_implies_second_fold_projection
    (V : FinalWord WideExact) (g : Fin 4 → SmallWord WideExact)
    (inputs : Inputs WideExact 5)
    (hpointsV : inputs.finalPoints 0 = finalNormalizedPoints V)
    (hpointsG : ∀ s : Fin 4,
      inputs.finalPoints (Fin.succ s) = finalNormalizedPoints (repeatedWord (g s)))
    (alpha : WideExact)
    (hgood : alpha ∉ AspisR1.SecondFoldMatched.secondBad g)
    (f : SmallMessage WideExact)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hvalid : ∀ i ∈ S, curveValue g alpha i = secondEncoder f i)
    (xs : RawCoins)
    (hnofail : ¬ AspisR1.GSConcreteByteDecoderBank.failed inputs xs) :
    ∃ raw : AspisR1.GSRejectingSamplerDecoderBank.FlatTape WideExact,
      M31RetryOutputFiber.actualWidePairSamplerTape 21377328 xs = some raw ∧
      ∃ out : Results WideExact 5,
        out = AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149 inputs
          (flatBank WideExact (1025*112) (256*112) 149 raw) ∧
        ∃ roots : Fin 5 → List (List WideExact),
          (∀ i : Fin 5, out.2 i = some (roots i)) ∧
        (∃ b : Fin 4 → SmallMessage WideExact,
          f = ∑ s : Fin 4, alpha ^ s.val • b s ∧
          (∀ s : Fin 4,
            b s ∈ projectFinalCandidates (filterCandidates (roots (Fin.succ s))) ∧
            AspisR1.sparseLift (b s) ∈ finalRuntimeCloseList
              (repeatedWord (g s)) (roots (Fin.succ s)))) := by
  classical
  change ¬ AspisR1.GSRejectingSamplerDecoderBank.failed
      (M31RetryOutputFiber.actualWidePairSamplerTape 21377328) (P31^8) inputs xs at hnofail
  obtain ⟨raw, hs, out, hout, roots, hroots⟩ :=
    AspisR1.GSNonfailureFinalRootsGeneric.nonfailure_yields_all_final_roots
      (M31RetryOutputFiber.actualWidePairSamplerTape 21377328) (P31^8) inputs xs hnofail
  have hrootsRun : ∀ i : Fin 5,
      (AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149 inputs
        (flatBank WideExact (1025*112) (256*112) 149 raw)).2 i = some (roots i) := by
    rw [← hout]
    exact hroots
  have hbank : ∀ i : Fin 5,
      (AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149 inputs
        (flatBank WideExact (1025*112) (256*112) 149 raw)).2 i = some (roots i) :=
    hrootsRun
  have hproj := second_match_five_lane_bank_success_includes_sparse
    V g alpha hgood f S hS hvalid (P31^8) 149 field_card
    (flatBank WideExact (1025*112) (256*112) 149 raw)
    inputs roots hpointsV hpointsG hbank
  exact ⟨raw, hs, out, hout, roots, hroots, hproj.2.2⟩


#print axioms byte_bank_nonfailure_implies_second_fold_projection

end AspisWide.GSConcreteSecondFoldByteBankProjectionGeneric
