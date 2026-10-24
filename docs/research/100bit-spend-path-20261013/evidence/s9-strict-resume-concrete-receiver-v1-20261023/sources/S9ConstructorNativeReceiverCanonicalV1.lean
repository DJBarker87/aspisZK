import S9FinishActualConstructorSlotV1
import S9ConstructorV3FactorsCanonicalV1
import S9ActualWeightsNewExtraExactV4
import S9PairSourceQMMulCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorNativeReceiverCanonicalV1
open AspisR1S9FinishActualConstructorSlotV1
abbrev Weights := AspisR1S9ProductionPairCutV1.weights.Weights
abbrev CWeights := AspisR1S9ActualWeightsNewBoxNewV3.Weights
abbrev CVector := AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1.Vector
abbrev CPoint := AspisR1S9ConstructorV3PointScanBodyCanonicalV1.Point
abbrev NQ := AspisR1S9ProductionPairCutV1.aspis_core.field.QM31
abbrev NCell := Array NQ 4#usize
abbrev NRow := Array NCell 5#usize
abbrev NPointRow := Array NQ 10#usize
abbrev mapArray := @AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def Canonical (q : NQ) : Prop := AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
  (AspisR1S9PairSourceQMMulCanonicalV1.toProbe q)
def FactorsCanonical (self : Weights) : Prop :=
  ∀ (k d : Usize) (row : NRow) (cell : NCell) (i : Usize) (q : NQ),
    Array.index_usize self.factors k = .ok row → Array.index_usize row d = .ok cell →
    Array.index_usize cell i = .ok q → Canonical q
def PointsCanonical (self : Weights) : Prop :=
  ∀ (k : Usize) (row : NPointRow) (i : Usize) (q : NQ),
    Array.index_usize self.points k = .ok row → Array.index_usize row i = .ok q → Canonical q
def ExtraCanonical (self : Weights) : Prop :=
  ∀ (i : Usize) (q : NQ), Array.index_usize self.extra i = .ok q → Canonical q

private theorem mapped_read_source {A B : Type} {n : Usize} (f : A → B)
    (a : Array A n) (i : Usize) (v : B)
    (h : Array.index_usize (mapArray f a) i = .ok v) :
    ∃ original, Array.index_usize a i = .ok original ∧ f original = v := by
  have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result f a i
  rw [h] at hm
  cases hr : Array.index_usize a i with
  | fail e => rw [hr] at hm; cases hm
  | div => rw [hr] at hm; cases hm
  | ok original => rw [hr] at hm; exact ⟨original,rfl,Result.ok.inj hm⟩

private theorem array_read_mem {A : Type} {n : Usize} (a : Array A n) (i : Usize) (v : A)
    (h : Array.index_usize a i = .ok v) : v ∈ a.val := by
  unfold Array.index_usize at h
  cases hr : a[i]? with
  | none => simp [hr] at h
  | some original =>
    have hi : a.val[i.val]? = some original := by simpa using hr
    rw [hr] at h
    have he : original = v := Result.ok.inj h
    exact he ▸ List.mem_of_getElem? hi

private theorem mapped_read {A B : Type} {n : Usize} (f : A → B)
    (a : Array A n) (i : Usize) (v : A) (h : Array.index_usize a i = .ok v) :
    Array.index_usize (mapArray f a) i = .ok (f v) := by
  have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result f a i
  rw [h] at hm
  exact hm.symm

/-- Complete 3D/2D native receiver coordinates retain the canonicality already
proved for the SAME V3 constructor result. No cell/row output is assumed. -/
theorem transported_receiver_canonical
    (w : CWeights)
    (hf : AspisR1S9ConstructorV3Loop2InnerCanonicalV1.FactorsCanonical w.factors)
    (hp : AspisR1S9ConstructorV3StatementCellCanonicalV1.StatementPointsCanonical w.points)
    (he : ∀ (i : Usize) (q : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31),
      Array.index_usize w.extra i = .ok q →
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.CanQ
        (AspisR1S9ConstructorV3Loop2InnerCanonicalV1.toProbeQ q)) :
    FactorsCanonical (fromCtorWeights w) ∧ PointsCanonical (fromCtorWeights w) ∧
      ExtraCanonical (fromCtorWeights w) := by
  constructor
  · intro k d row cell i q hrow hcell hq
    obtain ⟨cr,hcr,her⟩ := mapped_read_source (mapArray (mapArray fromCtorQM)) w.factors k row hrow
    rw [← her] at hcell
    obtain ⟨cc,hcc,hec⟩ := mapped_read_source (mapArray fromCtorQM) cr d cell hcell
    rw [← hec] at hq
    obtain ⟨cq,hcq,heq⟩ := mapped_read_source fromCtorQM cc i q hq
    have hrp := mapped_read AspisR1S9ConstructorV3Loop2InnerCanonicalV1.mapRow w.factors k cr hcr
    have hcp := mapped_read AspisR1S9ConstructorV3Loop2InnerCanonicalV1.mapCells cr d cc hcc
    have hqp := mapped_read AspisR1S9ConstructorV3Loop2InnerCanonicalV1.toProbeQ cc i cq hcq
    have hc := hf k _ hrp d _ hcp i _ hqp
    rw [← heq]
    exact hc
  · constructor
    · intro k row i q hrow hq
      obtain ⟨cr,hcr,her⟩ := mapped_read_source (mapArray fromCtorQM) w.points k row hrow
      rw [← her] at hq
      obtain ⟨cq,hcq,heq⟩ := mapped_read_source fromCtorQM cr i q hq
      have hc := hp k cr hcr i cq hcq
      rw [← heq]
      exact hc
    · intro i q hq
      obtain ⟨cq,hcq,heq⟩ := mapped_read_source fromCtorQM w.extra i q hq
      rw [← heq]
      exact he i cq hcq

/-- The concrete constructor slot's successful output has canonical native
factors, points and extras whenever its exact input contracts hold. Those
contracts are discharged by the same strict checkpoint resume producer in
the enclosing caller composition, not presumed as source/refinement facts. -/
theorem actual_constructor_slot_success_receiver_canonical
    (variant : AspisR1FinishRelationCurrent.transport.Variant)
    (alpha : Array AspisR1FinishRelationCurrent.aspis_core.field.QM31 10#usize)
    (z : Array AspisR1FinishRelationCurrent.aspis_core.circle.SecureCirclePoint 2#usize)
    (self : Weights)
    (halpha : AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1.VectorCanonical
      (mapArray toCtorQM alpha))
    (hz : AspisR1S9ConstructorV3PointScanBodyCanonicalV1.PointsCanonical (mapArray toCtorPoint z))
    (hnew : actualNewWeightsSlot variant alpha z = .ok (.Ok self)) :
    FactorsCanonical self ∧ PointsCanonical self ∧ ExtraCanonical self := by
  obtain ⟨w,hw,hself⟩ := actualNewWeightsSlot_success variant alpha z self hnew
  obtain ⟨hf,hp⟩ := AspisR1S9ConstructorV3FactorsCanonicalV1.constructor_success_factors_and_points_canonical
    (toCtorVariant variant) (mapArray toCtorQM alpha) (mapArray toCtorPoint z) w halpha hz hw
  obtain ⟨q8,q9,h8,h9,hextra⟩ := AspisR1S9ActualWeightsNewExtraExactV4.weights_new_extra_exact_v4
    (toCtorVariant variant) (mapArray toCtorQM alpha) (mapArray toCtorPoint z) w hw
  have he : ∀ (i : Usize) (q : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31),
      Array.index_usize w.extra i = .ok q →
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.CanQ
        (AspisR1S9ConstructorV3Loop2InnerCanonicalV1.toProbeQ q) := by
    intro i q hread
    have hm := array_read_mem w.extra i q hread
    rw [hextra] at hm
    change q ∈ [q8,q9] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · exact AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1.raw_read_canonical _ _ _ halpha h8
    · exact AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1.raw_read_canonical _ _ _ halpha h9
  rw [hself]
  exact transported_receiver_canonical w hf hp he

#print axioms transported_receiver_canonical
#print axioms actual_constructor_slot_success_receiver_canonical
end AspisR1S9ConstructorNativeReceiverCanonicalV1
