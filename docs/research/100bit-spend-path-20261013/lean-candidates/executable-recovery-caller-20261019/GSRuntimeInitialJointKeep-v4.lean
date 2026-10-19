import GSRuntimeDistanceEncoderBridge
import IncrementalCandidateLoop
import FiniteListCandidateMerge

set_option autoImplicit false

namespace AspisWide.GSRuntimeInitialJointKeep

open CompPoly
open AspisPool.AlgorithmicCircleDecoderV7
open AspisR1.PartialJointList
open AspisR1.IncrementalJointCandidates
open AspisR1.IncrementalCandidateLoop
open AspisR1.FiniteListCandidateMerge
open AspisWide.GSRuntimeDistanceEncoderBridge
open AspisWide.InitialEncoder
open AspisWide.WideExactGRSInstantiation
open AspisWideTower

variable [BEq WideExact] [LawfulBEq WideExact] [DecidableEq WideExact]
  [NeZero (2 : WideExact)] [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]
  [Fintype WideExact] [LawfulBEq (CPolynomial WideExact)]

/-- The runtime selected-coordinate support uses the computable CPolynomial
encoder. Its specification agrees pointwise with the established support. -/
def runtimeSelectedSupport (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord WideExact)
    (t : Fin 29 → InitialMessage WideExact) : Finset (Fin 1048576) :=
  Finset.univ.filter fun x =>
    ∀ lane, lane ∈ S → W lane x = initialRuntimeEncoder (t lane) x

theorem runtimeSelectedSupport_eq (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord WideExact)
    (t : Fin 29 → InitialMessage WideExact) :
    runtimeSelectedSupport S W t = selectedSupport S W t := by
  classical
  ext x
  simp [runtimeSelectedSupport, selectedSupport,
    initialRuntimeEncoder_eq_released]

/-- Actual Bool keep predicate used by the executable list merge. -/
def runtimeKeep (W : Fin 29 → InitialWord WideExact)
    (S : Finset (Fin 29)) (t : Fin 29 → InitialMessage WideExact) : Bool :=
  decide (38230 ≤ (runtimeSelectedSupport S W t).card)

theorem runtimeKeep_eq_legacy (W : Fin 29 → InitialWord WideExact)
    (S : Finset (Fin 29)) (t : Fin 29 → InitialMessage WideExact) :
    runtimeKeep W S t = decide (38230 ≤ (selectedSupport S W t).card) := by
  simp [runtimeKeep, runtimeSelectedSupport_eq]

theorem advanceSpec_eq_legacy (W : Fin 29 → InitialWord WideExact)
    (S : Finset (Fin 29)) (lane : Fin 29)
    (family : Finset (Fin 29 → InitialMessage WideExact))
    (decoded : Finset (InitialMessage WideExact)) :
    FiniteListCandidateMerge.advanceSpec (runtimeKeep W) S lane family decoded =
      IncrementalJointCandidates.advance S lane W family decoded := by
  ext t
  simp [FiniteListCandidateMerge.advanceSpec,
    IncrementalJointCandidates.advance, runtimeKeep_eq_legacy]

theorem runSpec_eq_legacy (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) (S : Finset (Fin 29))
    (family : Finset (Fin 29 → InitialMessage WideExact)) :
    FiniteListCandidateMerge.runSpec (runtimeKeep W)
        (fun i => (decoded i).toFinset) S family lanes =
      IncrementalCandidateLoop.run W
        (fun i => (decoded i).toFinset) S family lanes := by
  induction lanes generalizing S family with
  | nil => rfl
  | cons lane rest ih =>
      simp only [FiniteListCandidateMerge.runSpec, IncrementalCandidateLoop.run]
      rw [ih, advanceSpec_eq_legacy]

def runtimeCandidates (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) : List (Fin 29 → InitialMessage WideExact) :=
  FiniteListCandidateMerge.run (runtimeKeep W) decoded ∅ [fun _ => 0] lanes

theorem runtimeCandidates_toFinset (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) :
    (runtimeCandidates W decoded lanes).toFinset =
      IncrementalCandidateLoop.candidates W
        (fun i => (decoded i).toFinset) lanes := by
  rw [runtimeCandidates, FiniteListCandidateMerge.run_toFinset,
    runSpec_eq_legacy]
  simp [IncrementalCandidateLoop.candidates]

theorem runtimeCandidates_length_le_100 (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) :
    (runtimeCandidates W decoded lanes).length ≤ 100 := by
  apply FiniteListCandidateMerge.run_length_le
    (keep := runtimeKeep W) (decoded := decoded) (lanes := lanes)
    (S := ∅) (family := [fun _ => 0])
  · simp
  · rw [runSpec_eq_legacy]
    simpa [IncrementalCandidateLoop.candidates] using
      IncrementalCandidateLoop.candidates_card W
        (fun i => (decoded i).toFinset) lanes

#print axioms runtimeSelectedSupport
#print axioms runtimeSelectedSupport_eq
#print axioms runtimeKeep
#print axioms runtimeKeep_eq_legacy
#print axioms advanceSpec_eq_legacy
#print axioms runSpec_eq_legacy
#print axioms runtimeCandidates_toFinset
#print axioms runtimeCandidates_length_le_100

end AspisWide.GSRuntimeInitialJointKeep
