import EarlyC1Specialization

/-! The first 26 lanes of a late width29 tuple identify an earlier C1-only
object. Arbitrary late C2 words are explicit inputs, not assumed codewords. -/
set_option autoImplicit false
set_option maxRecDepth 80
set_option maxHeartbeats 5000
namespace AspisV8.EarlyC1LateProjection
open AspisV8.EarlyC1Projection AspisV8.EarlyC1Specialization
open AspisV8.NearGammaFibreBridge AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact

noncomputable local instance : Fintype (Fin 262144) := explicit_instance

abbrev C2Received := Fin 3 → Fin 1048576 → QM31Exact

def received29 (c1 : C1Received) (c2 : C2Received) :
    Fin 29 → Fin 1048576 → QM31Exact :=
  fun lane => if h : lane.val < 26 then c1 ⟨lane.val, h⟩
    else c2 ⟨lane.val - 26, by omega⟩

def fibreWord29 (c1 : C1Received) (c2 : C2Received) :
    Fin 29 → Fin 262144 → Fin 4 → QM31Exact :=
  fun lane fibre slot => received29 c1 c2 lane (fibreEmbed (fibre, slot))

def c1Projection (p : Fin 29 → Message) : C1Messages :=
  fun column => p (c1LaneIndex column)

theorem received29_c1 (c1 : C1Received) (c2 : C2Received) (column : Fin 26) :
    received29 c1 c2 (c1LaneIndex column) = c1 column := by
  simp [received29, c1LaneIndex]

theorem fibreWord29_c1 (c1 : C1Received) (c2 : C2Received)
    (column : Fin 26) (fibre : Fin 262144) :
    fibreWord29 c1 c2 (c1LaneIndex column) fibre = receivedFibres c1 column fibre := by
  funext slot
  exact congrFun (received29_c1 c1 c2 column) (fibreEmbed (fibre, slot))

theorem late_projection_identifies (c1 : C1Received) (c2 : C2Received)
    (p : Fin 29 → Message)
    (own : 245609 ≤ (support fibreEncode (fibreWord29 c1 c2) p).card) :
    earlyC1 c1 = some (c1Projection p) := by
  apply identify
  have subset := support_restrict fibreEncode (fibreWord29 c1 c2) p
    c1LaneIndex (receivedFibres c1) (fibreWord29_c1 c1 c2)
  exact own.trans (Finset.card_le_card subset)

theorem independent_of_late_C2 (c1 : C1Received) (c2 c2' : C2Received)
    (p p' : Fin 29 → Message)
    (own : 245609 ≤ (support fibreEncode (fibreWord29 c1 c2) p).card)
    (own' : 245609 ≤ (support fibreEncode (fibreWord29 c1 c2') p').card) :
    c1Projection p = c1Projection p' :=
  Option.some.inj ((late_projection_identifies c1 c2 p own).symm.trans
    (late_projection_identifies c1 c2' p' own'))

theorem none_excludes_qualifying_tuple (c1 : C1Received) (absent : earlyC1 c1 = none)
    (c2 : C2Received) (p : Fin 29 → Message) :
    ¬ 245609 ≤ (support fibreEncode (fibreWord29 c1 c2) p).card := by
  intro own
  have impossible := (late_projection_identifies c1 c2 p own).symm.trans absent
  cases impossible

#print axioms received29_c1
#print axioms fibreWord29_c1
#print axioms late_projection_identifies
#print axioms independent_of_late_C2
#print axioms none_excludes_qualifying_tuple
end AspisV8.EarlyC1LateProjection
