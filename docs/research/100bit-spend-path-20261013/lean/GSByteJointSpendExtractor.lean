import GSConcreteByteDecoderBank
import GSConcreteReceivedWordInputs
import GSActualRuntimeCloseCompleteness
import LiteralComputedCandidateExtract

set_option autoImplicit false
namespace AspisR1.GSByteJointSpendExtractor

open AspisWideTower AspisV8R15.ExactTowerBase SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSConcreteReceivedWordInputs
open AspisWide.GSRuntimeInitialDistanceEncoderBridge
open AspisWide.GSActualRuntimeCloseCompleteness
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSDecoderTapeReindex
open M31RetryOutputFiber M31AcceptFiber

abbrev K := WideExact
abbrev Coins := GSConcreteByteDecoderBank.RawCoins

def decodedLists (W : Fin 29 → InitialWord K) (out : Results K 5) :
    Fin 29 → List (InitialMessage K) :=
  fun lane => initialRuntimeCloseList (W lane) ((out.1 lane).getD [])

/-- Fixed received words are supplied before the fresh finite private tape.
The runtime bank feeds actual image/distance filters, joint merge and scan. -/
def extract (pub : R0P.Public M31Exact) (W : Fin 29 → InitialWord K)
    (V : Fin 5 → FinalWord K) (coins : Coins) : Option Wspend :=
  (GSConcreteByteDecoderBank.run (fromWords W V) coins).bind fun out =>
    LiteralComputedCandidateExtract.extract pub W (decodedLists W out)

theorem returned_valid (pub : R0P.Public M31Exact) (W : Fin 29 → InitialWord K)
    (V : Fin 5 → FinalWord K) (coins : Coins) (w : Wspend)
    (h : extract pub W V coins = some w) : Rspend pub w := by
  cases hr : GSConcreteByteDecoderBank.run (fromWords W V) coins with
  | none => simp only [extract, hr, Option.bind_none, reduceCtorEq] at h
  | some out =>
    have hw : LiteralComputedCandidateExtract.extract pub W
        (decodedLists W out) = some w := by
      simpa only [extract, hr, Option.bind_some] using h
    exact LiteralComputedCandidateExtract.returned_valid pub W _ w hw

attribute [local irreducible] AspisR1.GSConcreteRootRecovery.initial
  AspisR1.GSConcreteRootRecovery.final
  AspisR1.InitialResponses.Close

/-- Successful byte sampling and no actual bank abort supply the per-lane
completeness premise of the concrete joint witness scanner. -/
theorem decodedLists_complete (W : Fin 29 → InitialWord K)
    (V : Fin 5 → FinalWord K) (coins : Coins) (out : Results K 5)
    (hout : GSConcreteByteDecoderBank.run (fromWords W V) coins = some out)
    (hno : ¬ GSConcreteByteDecoderBank.failed (fromWords W V) coins) :
    ∀ lane, InitialResponses.Close (W lane) ⊆
      (decodedLists W out lane).toFinset := by
  have hnoOut : ¬ GSFixedInputDecoderFamily.failed out := by
    intro hf
    apply hno
    apply (GSRejectingSamplerDecoderBank.failed_iff_output
      (actualWidePairSamplerTape 21377328) (P31^8) (fromWords W V) coins).2
    exact Or.inr ⟨out, hout, hf⟩
  cases hs : actualWidePairSamplerTape 21377328 coins with
  | none =>
    simp only [GSConcreteByteDecoderBank.run,
      GSRejectingSamplerDecoderBank.sampleAndRun, hs, Option.map_none,
      reduceCtorEq] at hout
  | some H =>
    have heq : GSFixedInputDecoderFamily.run (P31^8) 149 (fromWords W V)
        (flatBank K (1025*112) (256*112) 149 H) = out := by
      apply Option.some.inj
      simpa only [GSConcreteByteDecoderBank.run,
        GSRejectingSamplerDecoderBank.sampleAndRun, hs, Option.map_some] using hout
    intro lane m hm
    cases hc : out.1 lane with
    | none => exact (hnoOut ⟨Sum.inl lane, hc⟩).elim
    | some cs =>
      have hcall : GSConcreteRootRecovery.initial (P31^8) 149
          ((fromWords W V).initialPoints lane)
          ((fromWords W V).initialSize lane)
          (flatBank K (1025*112) (256*112) 149 H).1 = some cs := by
        exact (congrArg (fun r : Results K 5 => r.1 lane) heq).trans hc
      have hclose := initial_call_success_runtime_list_to_Close (W lane)
        ((fromWords W V).initialPoints lane) (initialPoints_normalized W V lane)
        ((fromWords W V).initialSize lane) (P31^8) 149
        GSConcreteByteDecoderBank.field_card
        (flatBank K (1025*112) (256*112) 149 H).1 cs hcall
      have hm' : m ∈ (initialRuntimeCloseList (W lane) cs).toFinset := by
        rw [hclose]
        exact hm
      simpa only [decodedLists, hc, Option.getD_some] using hm'

#print axioms extract
#print axioms returned_valid
#print axioms decodedLists_complete
end AspisR1.GSByteJointSpendExtractor
