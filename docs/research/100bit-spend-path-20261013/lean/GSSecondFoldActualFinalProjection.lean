import GSActualFinalRuntimeCloseCompleteness
import GSFinalMessageCandidateFilter
import GSRuntimeFinalDistanceEncoderBridge
import SecondFoldSparseProjectionBridge
import SecondFoldSparseProjectionCore
import R1SecondFoldMatched
import AspisFormal.V7ExactOneFoldDomains
import GSFixedInputDecoderFamily
import RRFinalMessageRecovery

set_option autoImplicit false

namespace AspisWide.GSSecondFoldActualFinalProjection

open CompPoly.CBivariate
open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisR1.ConcreteProjection
open AspisWide.GSWideExactAgreementInputs
open AspisWide.GSActualFinalRuntimeCloseCompleteness
open AspisWide.GSFinalMessageCandidateFilter
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open AspisR1.RRFinalMessageRecovery
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.SecondFoldMatched
open AspisR1.SecondFoldSparseProjectionCore
open AspisR1.SecondFoldSparseProjectionBridge
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriCoherentCandidateExtraction

/-- A successful actual final call turns its exact decoder list into both the
runtime close-list witness and the sparse projected-candidate witness. -/
theorem successful_final_decode_includes_sparse
    (received : SmallWord WideExact)
    (points : Array (WideExact × WideExact))
    (hpoints : points = finalNormalizedPoints (repeatedWord received))
    (hsize : points.size = 262144)
    (q t : Nat) (hq : q = Fintype.card WideExact)
    (H : InitialTape WideExact t × FinalTape WideExact t)
    (roots : List (List WideExact))
    (hraw : AspisR1.GSConcreteRootRecovery.final q t points hsize H.2 = some roots)
    (m : SmallMessage WideExact)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hmatch : ∀ i ∈ S, secondEncoder m i = received i) :
    m ∈ projectFinalCandidates (filterCandidates roots) ∧
      AspisR1.sparseLift m ∈ finalRuntimeCloseList (repeatedWord received) roots := by
  classical
  have hdecode : ∀ a : Fin 256 → WideExact,
      9558 ≤ (agreementSet
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) a)
        (repeatedWord received)).card → a ∈ filterCandidates roots := by
    intro a hagree
    have hcount : agreementCount (repeatedWord received)
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) a) =
        (agreementSet (AspisWide.FinalEncoder.exactFinalEncoder
          (K := WideExact) a) (repeatedWord received)).card := by
      have hsets : Finset.univ.filter (fun i => repeatedWord received i =
          AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) a i) =
          Finset.univ.filter (fun i => AspisWide.FinalEncoder.exactFinalEncoder
            (K := WideExact) a i = repeatedWord received i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
      exact congrArg Finset.card hsets
    have hclose : closeAtLeast 9558
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
        (repeatedWord received) a := by
      change 9558 ≤ agreementCount (repeatedWord received)
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) a)
      rw [hcount]
      exact hagree
    have hruntime := (final_call_success_runtime_close_iff
      (repeatedWord received) points hpoints hsize q t hq H.2 roots hraw a).2 hclose
    exact (finalRuntimeCloseList_mem_iff (repeatedWord received) roots a).mp
      hruntime |>.1
  have hprojected := second_match_survives_projection received m S hS hmatch
    (filterCandidates roots) hdecode
  have hagree : 9558 ≤ (agreementSet
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) (AspisR1.sparseLift m))
      (repeatedWord received)).card :=
    sparseLift_final_agreement_of_second_match received m S hS hmatch
  have hcount : agreementCount (repeatedWord received)
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) (AspisR1.sparseLift m)) =
      (agreementSet (AspisWide.FinalEncoder.exactFinalEncoder
        (K := WideExact) (AspisR1.sparseLift m)) (repeatedWord received)).card := by
    have hsets : Finset.univ.filter (fun i => repeatedWord received i =
        AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) (AspisR1.sparseLift m) i) =
        Finset.univ.filter (fun i => AspisWide.FinalEncoder.exactFinalEncoder
          (K := WideExact) (AspisR1.sparseLift m) i = repeatedWord received i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
    exact congrArg Finset.card hsets
  have hclose : closeAtLeast 9558
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
      (repeatedWord received) (AspisR1.sparseLift m) := by
    change 9558 ≤ agreementCount (repeatedWord received)
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) (AspisR1.sparseLift m))
    rw [hcount]
    exact hagree
  have hruntime := (final_call_success_runtime_close_iff
    (repeatedWord received) points hpoints hsize q t hq H.2 roots hraw
    (AspisR1.sparseLift m)).2 hclose
  exact ⟨hprojected, hruntime⟩

/-- The five-output final bank keeps its V lane and four distinct repeated
channel words. Every successful output in a channel lane yields the sparse
projection promised by the second-fold relation. -/
theorem second_match_five_lane_bank_success_includes_sparse
    (V : FinalWord WideExact)
    (g : Fin 4 → SmallWord WideExact)
    (alpha : WideExact)
    (hgood : alpha ∉ AspisR1.SecondFoldMatched.secondBad g)
    (f : SmallMessage WideExact)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hvalid : ∀ i ∈ S, curveValue g alpha i = secondEncoder f i)
    (q t : Nat) (hq : q = Fintype.card WideExact)
    (H : InitialTape WideExact t × FinalTape WideExact t)
    (inputs : AspisR1.GSFixedInputDecoderFamily.Inputs WideExact 5)
    (roots : Fin 5 → List (List WideExact))
    (hpointsV : inputs.finalPoints 0 = finalNormalizedPoints V)
    (hpointsG : ∀ s : Fin 4,
      inputs.finalPoints (Fin.succ s) =
        finalNormalizedPoints (repeatedWord (g s)))
    (hbank : ∀ i : Fin 5,
      (AspisR1.GSFixedInputDecoderFamily.run q t inputs H).2 i = some (roots i)) :
    inputs.finalPoints 0 = finalNormalizedPoints V ∧
      (AspisR1.GSFixedInputDecoderFamily.run q t inputs H).2 0 = some (roots 0) ∧
      ∃ b : Fin 4 → SmallMessage WideExact,
      f = ∑ s : Fin 4, alpha ^ s.val • b s ∧
      (∀ s : Fin 4,
        b s ∈ projectFinalCandidates (filterCandidates (roots (Fin.succ s))) ∧
        AspisR1.sparseLift (b s) ∈ finalRuntimeCloseList
          (repeatedWord (g s)) (roots (Fin.succ s))) := by
  have hrawV := hbank 0
  obtain ⟨b, hb, hf⟩ := AspisR1.SecondFoldMatched.second_match
    g alpha hgood f S hS hvalid
  refine ⟨hpointsV, hrawV, b, hf, ?_⟩
  intro s
  have hraw : AspisR1.GSConcreteRootRecovery.final q t
      (inputs.finalPoints (Fin.succ s))
      (inputs.finalSize (Fin.succ s)) H.2 = some (roots (Fin.succ s)) := by
    simpa only [AspisR1.GSFixedInputDecoderFamily.run] using hbank (Fin.succ s)
  have hsize : (inputs.finalPoints (Fin.succ s)).size = 262144 :=
    inputs.finalSize (Fin.succ s)
  have hmatch : ∀ i ∈ S, secondEncoder (b s) i = g s i := by
    intro i hi
    exact (hb i hi s).symm
  exact successful_final_decode_includes_sparse (g s)
    (inputs.finalPoints (Fin.succ s)) (hpointsG s) hsize q t hq H
    (roots (Fin.succ s)) hraw (b s) S hS hmatch

#print axioms successful_final_decode_includes_sparse
#print axioms second_match_five_lane_bank_success_includes_sparse

end AspisWide.GSSecondFoldActualFinalProjection
