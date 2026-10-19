import GSConcreteSecondFoldByteBankFromWordsGeneric
import R1MatchingSupport

set_option autoImplicit false

namespace AspisWide.GSConcreteSecondFoldModelByteBankProjection

open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisR1.MatchingSupport
open AspisR1.ConcreteBinding
open AspisR1.SecondFoldRestoration
open AspisR1.SecondFoldMatched
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSConcreteByteDecoderBank
open AspisR1.GSDecoderTapeReindex
open M31AcceptFiber
open AspisV8R19.OracleResampling
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisR1.GSRejectingSamplerDecoderBank
open AspisWide.GSConcreteReceivedWordInputs
open AspisWide.GSConcreteSecondFoldByteBankFromWords

attribute [local irreducible] AspisR1.SecondFoldRestoration.channels

/-- The retained matching-support model supplies precisely the two premises
needed by the second-fold decoder projection: the alpha1 bad-set exclusion,
and a 2390-parent support on which the second-fold equation holds.  No source,
challenge, or matching hypothesis is silently discarded. -/
theorem model_nonfailure_implies_second_fold_projection
    (d : AspisR1.MatchingSupport.Data WideExact)
    (hgoodModel : AspisR1.MatchingSupport.Good d)
    (hcard : 9558 ≤ (AspisR1.MatchingSupport.matchingSet d).card)
    (xs : RawCoins)
    (hnofail : ¬ AspisR1.GSConcreteByteDecoderBank.failed
      (fromWords d.W
        (Fin.cases d.V
          (fun s => repeatedWord (AspisR1.SecondFoldRestoration.channels d.V s)))) xs) :
    ∃ raw : AspisR1.GSRejectingSamplerDecoderBank.FlatTape WideExact,
      M31RetryOutputFiber.actualWidePairSamplerTape 21377328 xs = some raw ∧
      ∃ out : Results WideExact 5,
        out = AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149
          (AspisWide.GSConcreteReceivedWordInputs.fromWords d.W
            (Fin.cases d.V
              (fun s => repeatedWord (AspisR1.SecondFoldRestoration.channels d.V s))) )
          (flatBank WideExact (1025*112) (256*112) 149 raw) ∧
        ∃ roots : Fin 5 → List (List WideExact),
          (∀ i : Fin 5, out.2 i = some (roots i)) ∧
          (∃ b : Fin 4 → AspisR1.ConcreteProjection.SmallMessage WideExact,
            d.f = ∑ s : Fin 4, d.alpha1 ^ s.val • b s ∧
            (∀ s : Fin 4,
              b s ∈ AspisR1.SecondFoldSparseProjectionCore.projectFinalCandidates (AspisWide.GSFinalMessageCandidateFilter.filterCandidates (roots (Fin.succ s))) ∧
              AspisR1.sparseLift (b s) ∈ AspisWide.GSRuntimeFinalDistanceEncoderBridge.finalRuntimeCloseList
                (repeatedWord (AspisR1.SecondFoldRestoration.channels d.V s))
                (roots (Fin.succ s)))) := by
  classical
  rcases hgoodModel with ⟨_, _, _, _, hsecond⟩
  have hsecondParts :
      d.alpha1 ∉ AspisR1.SecondFoldMatched.secondBad
          (AspisR1.SecondFoldRestoration.channels d.V) ∧
      d.alpha1 ∉ AspisR1.TwoRoundComparison.comparisonBad
          (AspisR1.ConcreteBinding.candidates d.W) d.p1
          (AspisR1.TwoRoundPairing.round1Truth (n := 64) d.alpha0
            (AspisR1.ConcreteBinding.batches d.gamma)
            (AspisR1.FunctionalWeights.weights d.F d.F0 d.kappa)) := by
    have hsecond' : d.alpha1 ∉
        (AspisR1.SecondFoldMatched.secondBad
          (AspisR1.SecondFoldRestoration.channels d.V) ∪
         AspisR1.TwoRoundComparison.comparisonBad
          (AspisR1.ConcreteBinding.candidates d.W) d.p1
          (AspisR1.TwoRoundPairing.round1Truth (n := 64) d.alpha0
            (AspisR1.ConcreteBinding.batches d.gamma)
            (AspisR1.FunctionalWeights.weights d.F d.F0 d.kappa))) := by
      change d.alpha1 ∉ AspisR1.ConcreteBinding.secondBad d.W d.V d.gamma d.alpha0
        (AspisR1.FunctionalWeights.weights d.F d.F0 d.kappa) d.p1 at hsecond
      exact hsecond
    simpa only [Finset.mem_union, not_or] using hsecond' 
  letI : DecidableEq (Fin 65536) := AspisR1.instDecidableEqFin_r1ParentSupport
  let S : Finset (Fin 65536) :=
    AspisR1.parentSupport (n := 65536) (AspisR1.MatchingSupport.matchingSet d)
  have hS : 2390 ≤ S.card := by
    exact AspisR1.parentSupport_card_ge_2390_65536
      (AspisR1.MatchingSupport.matchingSet d) hcard
  have hvalid : ∀ i ∈ S,
      curveValue (AspisR1.SecondFoldRestoration.channels d.V) d.alpha1 i =
        AspisR1.ConcreteProjection.secondEncoder d.f i := by
    intro i hi
    obtain ⟨k, hk, hparent⟩ := Finset.mem_image.mp hi
    have hmatch : AspisR1.MatchingSupport.match1 d k :=
      (Finset.mem_filter.mp hk).2.2
    simp only [AspisR1.MatchingSupport.match1] at hmatch
    change curveValue (AspisR1.SecondFoldRestoration.channels d.V) d.alpha1
        (AspisR1.parentIndex k) = AspisR1.ConcreteProjection.secondEncoder d.f
          (AspisR1.parentIndex k) at hmatch
    rw [hparent] at hmatch
    exact hmatch
  have hwords := AspisWide.GSConcreteSecondFoldByteBankFromWords.byte_bank_nonfailure_implies_second_fold_projection_from_words
    d.W d.V (AspisR1.SecondFoldRestoration.channels d.V) d.alpha1 hsecondParts.1
    d.f S hS hvalid xs hnofail
  exact hwords

#print axioms model_nonfailure_implies_second_fold_projection

end AspisWide.GSConcreteSecondFoldModelByteBankProjection
