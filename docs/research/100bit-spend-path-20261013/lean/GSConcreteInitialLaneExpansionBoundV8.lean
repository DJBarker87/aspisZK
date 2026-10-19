import GSRuntimeInitialJointKeepCore
import GSRuntimeCandidateListLength
import GSActualListExpansionBound
import GSRuntimeInitialDistanceEncoderBridge
import GSConcreteRecoveryOutputLength

set_option autoImplicit false
namespace AspisWide.GSConcreteInitialLaneExpansionBoundV8
open CompPoly AspisWideTower AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSRuntimeInitialJointKeepCore
open AspisWide.GSRuntimeCandidateListLength
open AspisWide.GSRuntimeInitialDistanceEncoderBridge
open AspisR1.GSConcreteRootRecoveryOutputLength
open AspisR1.GSActualListExpansionBound

/-- The actual per-lane merge expansion is bounded even when the 29 decoded
lists differ. The selected lane is tied to its concrete successful recovery
and runtime image/distance filter; all other lists remain the actual inputs to
the maintained joint-candidate implementation. -/
theorem actual_initial_lane_expansion_length_le_11200
    [BEq WideExact] [LawfulBEq WideExact] [DecidableEq WideExact]
    [NeZero (2 : WideExact)]
    [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]
    [Fintype WideExact] [LawfulBEq (CPolynomial WideExact)]
    (q t : Nat) (points : Array (WideExact × WideExact))
    (hs : points.size = 1048576) (hq : q = Fintype.card WideExact)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → WideExact × WideExact)
    (raw : List (List WideExact))
    (hout : AspisR1.GSConcreteRootRecovery.initial q t points hs H = some raw)
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m)
    (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) (lane : Fin 29)
    (hdecoded : decoded lane = initialRuntimeCloseList (W lane) raw) :
    (laneExpansion lane (runtimeCandidates enc W decoded lanes) (decoded lane)).length ≤ 11200 := by
  have hfamily := runtimeCandidates_length_le_100 enc henc W decoded lanes
  have hrawLength := initial_output_length_le_112 q t points hs hq H raw hout
  have hcloseLength := initialRuntimeCloseList_length_le_112 (W lane) raw hrawLength
  have hdecodedLength : (decoded lane).length ≤ 112 := by rw [hdecoded]; exact hcloseLength
  exact laneExpansion_length_le_100_112 lane
    (runtimeCandidates enc W decoded lanes) (decoded lane) hfamily hdecodedLength

#print axioms actual_initial_lane_expansion_length_le_11200
end AspisWide.GSConcreteInitialLaneExpansionBoundV8
