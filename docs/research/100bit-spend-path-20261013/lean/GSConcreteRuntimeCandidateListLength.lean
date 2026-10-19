import GSRuntimeInitialDistanceEncoderBridge
import GSRuntimeFinalDistanceEncoderBridge
import GSRuntimeCandidateListLength
import GSRuntimeFinalCandidateListLength
import GSConcreteRootRecovery
import RRFixedTapeRecoveryOutputLength

set_option autoImplicit false
namespace AspisWide.GSConcreteRuntimeCandidateListLength
open AspisWideTower AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSRuntimeInitialDistanceEncoderBridge
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open AspisWide.GSRuntimeCandidateListLength
open AspisWide.GSRuntimeFinalCandidateListLength
open AspisR1.GSConcreteRootRecovery
open AspisR1.RRFixedTapeRecovery
open AspisR1.RRFixedTapeRecoveryOutputLength

theorem initial_runtime_close_list_length_le_112 (q t : Nat)
    (points : Array (WideExact × WideExact)) (hs : points.size = 1048576)
    (hq : q = Fintype.card WideExact)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → WideExact × WideExact)
    (received : InitialWord WideExact) (cs : List (List WideExact))
    (hout : initial q t points hs H = some cs) :
    (initialRuntimeCloseList received cs).length ≤ 112 := by
  obtain ⟨Q, hr, _⟩ := AspisR1.GSConcreteInterpolation.initial_exists points hs
  have hc := AspisR1.GSConcreteInterpolation.initial_state_contract points hs Q hr
  have hrecover :
      (recover 112 q t 1025 (AspisR1.GSConcreteInterpolation.initialState Q)
        hc.2.1 hc.2.2 H).1 = some cs := by
    rw [← initial_eq_recovery q t points hs Q hr H]
    exact hout
  have hlen := recover_output_length_le 112 q t 1025
    (AspisR1.GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 hq H cs hrecover
  exact initialRuntimeCloseList_length_le_112 received cs hlen

theorem final_runtime_close_list_length_le_112 (q t : Nat)
    (points : Array (WideExact × WideExact)) (hs : points.size = 262144)
    (hq : q = Fintype.card WideExact)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → WideExact × WideExact)
    (received : FinalWord WideExact) (cs : List (List WideExact))
    (hout : final q t points hs H = some cs) :
    (finalRuntimeCloseList received cs).length ≤ 112 := by
  obtain ⟨Q, hr, _⟩ := AspisR1.GSConcreteInterpolation.final_exists points hs
  have hc := AspisR1.GSConcreteInterpolation.final_state_contract points hs Q hr
  have hrecover :
      (recover 112 q t 256 (AspisR1.GSConcreteInterpolation.finalState Q)
        hc.2.1 hc.2.2 H).1 = some cs := by
    rw [← final_eq_recovery q t points hs Q hr H]
    exact hout
  have hlen := recover_output_length_le 112 q t 256
    (AspisR1.GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 hq H cs hrecover
  exact finalRuntimeCloseList_length_le_112 received cs hlen

#print axioms initial_runtime_close_list_length_le_112
#print axioms final_runtime_close_list_length_le_112
end AspisWide.GSConcreteRuntimeCandidateListLength
