import WideTower
import Wide.Initial
import R1InitialResponses
import R1IncrementalCandidateLoop
import R1ConcreteBinding
import FiniteListCandidateMerge

set_option autoImplicit false

namespace AspisWide.GSRuntimeInitialJointKeepCore

open AspisPool.AlgorithmicCircleDecoderV7
open AspisWideTower

variable [BEq WideExact] [LawfulBEq WideExact] [DecidableEq WideExact]
  [NeZero (2 : WideExact)] [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]
  [Fintype WideExact]

/-- The runtime selected-coordinate support uses the computable CPolynomial
encoder. Its specification agrees pointwise with the established support. -/
def runtimeSelectedSupport (enc : InitialMessage WideExact → InitialWord WideExact)
    (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord WideExact)
    (t : Fin 29 → InitialMessage WideExact) : Finset (Fin 1048576) :=
  Finset.univ.filter fun x =>
    ∀ lane, lane ∈ S → W lane x = enc (t lane) x

theorem runtimeSelectedSupport_eq
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m) (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord WideExact)
    (t : Fin 29 → InitialMessage WideExact) :
    runtimeSelectedSupport enc S W t = AspisR1.PartialJointList.selectedSupport S W t := by
  classical
  ext x
  simp [runtimeSelectedSupport, AspisR1.PartialJointList.selectedSupport, henc]

/-- Actual Bool keep predicate used by the executable list merge. -/
def runtimeKeep (enc : InitialMessage WideExact → InitialWord WideExact)
    (W : Fin 29 → InitialWord WideExact)
    (S : Finset (Fin 29)) (t : Fin 29 → InitialMessage WideExact) : Bool :=
  decide (38230 ≤ (runtimeSelectedSupport enc S W t).card)

theorem runtimeKeep_eq_legacy
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m) (W : Fin 29 → InitialWord WideExact)
    (S : Finset (Fin 29)) (t : Fin 29 → InitialMessage WideExact) :
    runtimeKeep enc W S t = decide (38230 ≤ (AspisR1.PartialJointList.selectedSupport S W t).card) := by
  simp [runtimeKeep, runtimeSelectedSupport_eq enc henc]

theorem advanceSpec_eq_legacy
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m) (W : Fin 29 → InitialWord WideExact)
    (S : Finset (Fin 29)) (lane : Fin 29)
    (family : Finset (Fin 29 → InitialMessage WideExact))
    (decoded : Finset (InitialMessage WideExact)) :
    AspisR1.FiniteListCandidateMerge.advanceSpec (runtimeKeep enc W) S lane family decoded =
      AspisR1.IncrementalJointCandidates.advance S lane W family decoded := by
  ext t
  simp [AspisR1.FiniteListCandidateMerge.advanceSpec,
    AspisR1.IncrementalJointCandidates.advance, runtimeKeep_eq_legacy enc henc]

theorem runSpec_eq_legacy
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m) (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) (S : Finset (Fin 29))
    (family : Finset (Fin 29 → InitialMessage WideExact)) :
    AspisR1.FiniteListCandidateMerge.runSpec (runtimeKeep enc W)
        (fun i => (decoded i).toFinset) S family lanes =
      AspisR1.IncrementalCandidateLoop.run W
        (fun i => (decoded i).toFinset) S family lanes := by
  induction lanes generalizing S family with
  | nil => rfl
  | cons lane rest ih =>
      simp only [AspisR1.FiniteListCandidateMerge.runSpec, AspisR1.IncrementalCandidateLoop.run]
      rw [ih, advanceSpec_eq_legacy enc henc]

def runtimeCandidates (enc : InitialMessage WideExact → InitialWord WideExact)
    (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) : List (Fin 29 → InitialMessage WideExact) :=
  AspisR1.FiniteListCandidateMerge.run (runtimeKeep enc W) decoded ∅ [0] lanes

theorem runtimeCandidates_toFinset
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m) (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) :
    (runtimeCandidates enc W decoded lanes).toFinset =
      AspisR1.IncrementalCandidateLoop.candidates W
        (fun i => (decoded i).toFinset) lanes := by
  rw [runtimeCandidates, AspisR1.FiniteListCandidateMerge.run_toFinset,
    runSpec_eq_legacy enc henc]
  simp [AspisR1.IncrementalCandidateLoop.candidates]

theorem runtimeCandidates_length_le_100
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m)
    (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29)) :
    (runtimeCandidates enc W decoded lanes).length ≤ 100 := by
  apply AspisR1.FiniteListCandidateMerge.run_length_le
    (keep := runtimeKeep enc W) (decoded := decoded) (lanes := lanes)
    (S := ∅) (family := [0])
  · simp
  · rw [runSpec_eq_legacy enc henc]
    simpa [AspisR1.IncrementalCandidateLoop.candidates] using
      AspisR1.IncrementalCandidateLoop.candidates_card W
        (fun i => (decoded i).toFinset) lanes


theorem runtimeCandidates_to_lambda
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m)
    (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29))
    (hcover : lanes.toFinset = Finset.univ)
    (hcomplete : ∀ lane, AspisR1.InitialResponses.Close (W lane) ⊆ (decoded lane).toFinset) :
    (runtimeCandidates enc W decoded lanes).toFinset = AspisR1.InitialResponses.Lambda W := by
  rw [runtimeCandidates_toFinset enc henc W decoded lanes]
  exact AspisR1.IncrementalCandidateLoop.candidates_eq_lambda W
    (fun i => (decoded i).toFinset) lanes hcover hcomplete

theorem runtimeCandidates_to_bindingCandidates
    (enc : InitialMessage WideExact → InitialWord WideExact)
    (henc : ∀ m, enc m = AspisWide.InitialEncoder.exactInitialEncoder m)
    (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (lanes : List (Fin 29))
    (hcover : lanes.toFinset = Finset.univ)
    (hcomplete : ∀ lane, AspisR1.InitialResponses.Close (W lane) ⊆ (decoded lane).toFinset) :
    (runtimeCandidates enc W decoded lanes).toFinset = AspisR1.ConcreteBinding.candidates W := by
  rw [runtimeCandidates_to_lambda enc henc W decoded lanes hcover hcomplete]
  rfl

#print axioms runtimeSelectedSupport
#print axioms runtimeSelectedSupport_eq
#print axioms runtimeKeep
#print axioms runtimeKeep_eq_legacy
#print axioms advanceSpec_eq_legacy
#print axioms runSpec_eq_legacy
#print axioms runtimeCandidates_toFinset
#print axioms runtimeCandidates_length_le_100
#print axioms runtimeCandidates_to_lambda
#print axioms runtimeCandidates_to_bindingCandidates

end AspisWide.GSRuntimeInitialJointKeepCore
