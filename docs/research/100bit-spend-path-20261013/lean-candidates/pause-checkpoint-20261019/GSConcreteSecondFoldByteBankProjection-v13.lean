import GSConcreteByteDecoderBankClosedEquality
import GSConcreteByteDecoderBank
import GSRejectingSamplerDecoderBank
import M31PairedWideSamplerLaw
import M31AcceptFiber
import GSSecondFoldActualFinalProjection

set_option autoImplicit false

namespace AspisWide.GSConcreteSecondFoldByteBankProjection

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
attribute [local irreducible] AspisR1.GSConcreteRootRecovery.initial
attribute [local irreducible] AspisR1.GSConcreteRootRecovery.final

/-- If the actual byte sampler and decoder bank do not fail, its sampled
finite tape supplies all five successful final decoder lists. -/
theorem nonfailure_yields_all_final_roots
    (inputs : Inputs WideExact 5) (xs : RawCoins)
    (hnofail : ¬ AspisR1.GSConcreteByteDecoderBank.failed inputs xs) :
    ∃ raw : AspisR1.GSRejectingSamplerDecoderBank.FlatTape WideExact,
      M31RetryOutputFiber.actualWidePairSamplerTape 21377328 xs = some raw ∧
      ∃ out : Results WideExact 5,
        out = AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149 inputs
          (flatBank WideExact (1025*112) (256*112) 149 raw) ∧
        ∃ roots : Fin 5 → List (List WideExact),
          ∀ i : Fin 5, out.2 i = some (roots i) := by
  classical
  change ¬ AspisR1.GSRejectingSamplerDecoderBank.failed
      (M31RetryOutputFiber.actualWidePairSamplerTape 21377328) (P31^8) inputs xs at hnofail
  cases hs : M31RetryOutputFiber.actualWidePairSamplerTape 21377328 xs with
  | none =>
      have hbad : AspisR1.GSRejectingSamplerDecoderBank.failed
          (M31RetryOutputFiber.actualWidePairSamplerTape 21377328) (P31^8) inputs xs := by
        exact (AspisR1.GSRejectingSamplerDecoderBank.failed_iff_output (M31RetryOutputFiber.actualWidePairSamplerTape 21377328)
          (P31^8) inputs xs).2 (Or.inl (by simp [AspisR1.GSRejectingSamplerDecoderBank.sampleAndRun, hs]))
      exact False.elim (hnofail hbad)
  | some raw =>
      let H := flatBank WideExact (1025*112) (256*112) 149 raw
      let out := AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149 inputs H
      have houtbad : ¬ AspisR1.GSFixedInputDecoderFamily.failed out := by
        intro hbad
        apply hnofail
        exact (AspisR1.GSRejectingSamplerDecoderBank.failed_iff_output (M31RetryOutputFiber.actualWidePairSamplerTape 21377328)
          (P31^8) inputs xs).2 (Or.inr ⟨out, by simp [AspisR1.GSRejectingSamplerDecoderBank.sampleAndRun, hs, out, H], hbad⟩)
      have hsuccess : ∀ i : Fin 5, ∃ r,
          out.2 i = some r := by
        intro i
        have hne : out.2 i ≠ none := by
          intro hn
          apply houtbad
          exact ⟨Sum.inr i, by simp [AspisR1.GSFixedInputDecoderFamily.failed, hn]⟩
        cases hi : out.2 i with
        | none => exact False.elim (hne hi)
        | some r => exact ⟨r, rfl⟩
      choose roots hroots using hsuccess
      have houtRun : out = AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149 inputs H := rfl
      have hrootWitness : ∃ roots : Fin 5 → List (List WideExact),
          ∀ i : Fin 5, out.2 i = some (roots i) := ⟨roots, hroots⟩
      have hrunWitness : ∃ result : Results WideExact 5,
          result = AspisR1.GSFixedInputDecoderFamily.run (P31^8) 149 inputs H ∧
            ∃ roots : Fin 5 → List (List WideExact),
              ∀ i : Fin 5, result.2 i = some (roots i) :=
        ⟨out, ⟨houtRun, hrootWitness⟩⟩
      exact ⟨raw, rfl, hrunWitness⟩

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
  obtain ⟨raw, hs, out, hout, roots, hroots⟩ :=
    nonfailure_yields_all_final_roots inputs xs hnofail
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

#print axioms nonfailure_yields_all_final_roots
#print axioms byte_bank_nonfailure_implies_second_fold_projection

end AspisWide.GSConcreteSecondFoldByteBankProjection
