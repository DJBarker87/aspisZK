import R1Z.PV_OWNM_SourceDense
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNM_ConcreteRestore
open Aeneas Aeneas.Std Result PV_OWNI_RawOps PV_OWNM_V239
abbrev K := PV_OWNK_ConcreteDecoder.K
abbrev decode := PV_OWNK_ConcreteDecoder.decode

/-- The scalar commutation hypothesis of the skeleton is discharged and consumed.
Actual-input, operational byte-frame and owned-source instances are still named
hypotheses, not silently supplied by independent model invariants. -/
theorem restore {W : Type}
 (wirePoints : List Q → List (List Q)) (isBoolean : Q → Bool)
 (reconstruct879 reconstruct890 : Public → List Q)
 (native : Input → List Q → Nat → Execution K W)
 (resource : Input → List Q → Nat → ResourceExit W)
 (failures : List Bool) (left right : Input)
 (inputL : PV_OWNM_Link_ActualInput wirePoints left)
 (inputR : PV_OWNM_Link_ActualInput wirePoints right)
 (cbL : PV_OWNM_Link_Transcript879 reconstruct879 left)
 (cbR : PV_OWNM_Link_Transcript879 reconstruct879 right)
 (finalL : PV_OWNM_Link_Transcript890 reconstruct890 left)
 (finalR : PV_OWNM_Link_Transcript890 reconstruct890 right)
 (ownedL : PV_OWNM_Link_OwnedPublicPlan decode PV_OWNM_SourceDense.source222
  wirePoints isBoolean native resource failures left)
 (ownedR : PV_OWNM_Link_OwnedPublicPlan decode PV_OWNM_SourceDense.source222
  wirePoints isBoolean native resource failures right)
 (samePublic : left.pubData = right.pubData) (sameSite : left.site = right.site)
 (sameLengths : left.columns.map List.length = right.columns.map List.length) :
 (∀ p ∈ wirePoints left.point, ∀ lane c, left.columns[lane]? = some c →
  native left p lane = attach (resource left p lane)
   (ok (if c.length ≠ 1024 then none else some (dense decode zero p c)))) ∧
 (∀ p ∈ wirePoints right.point, ∀ lane c, right.columns[lane]? = some c →
  native right p lane = attach (resource right p lane)
   (ok (if c.length ≠ 1024 then none else some (dense decode zero p c)))) ∧
 (∀ pL ∈ wirePoints left.point, ∀ pR ∈ wirePoints right.point,
  ∀ laneL laneR cL cR, left.columns[laneL]? = some cL →
  right.columns[laneR]? = some cR →
  (native left pL laneL).trace = (native right pR laneR).trace) :=
 PV_OWNM_V239.restore decode zero PV_OWNM_SourceDense.source222 wirePoints isBoolean
  reconstruct879 reconstruct890 native resource failures left right inputL inputR
  PV_OWNM_SourceDense.concrete_source_dense cbL cbR finalL finalR ownedL ownedR
  samePublic sameSite sameLengths

#print axioms restore
end R1Z.PV_OWNM_ConcreteRestore
