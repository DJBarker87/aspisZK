import S9FinishActualPairSlotV1
import S9ConstructorV3VariantPreservedV1
import S9CandidateFoldMapPrimitivesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FinishActualConstructorSlotV1
abbrev mapArray := @AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
abbrev Weights := AspisR1S9FinishActualPairSlotV1.Weights
abbrev CQ := AspisR1S9ActualWeightsNewBoxNewV3.field.QM31
abbrev NQ := AspisR1S9ProductionPairCutV1.aspis_core.field.QM31
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def toCtorVariant : AspisR1FinishRelationCurrent.transport.Variant → AspisR1S9ActualWeightsNewBoxNewV3.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D
def fromCtorVariant : AspisR1S9ActualWeightsNewBoxNewV3.Variant → AspisR1S9ProductionPairCutV1.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D
def toCtorQM (x : AspisR1FinishRelationCurrent.aspis_core.field.QM31) : CQ :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toCtorPoint (x : AspisR1FinishRelationCurrent.aspis_core.circle.SecureCirclePoint) :
    AspisR1S9ActualWeightsNewBoxNewV3.circle.SecureCirclePoint := ⟨toCtorQM x.x,toCtorQM x.y⟩
def fromCtorQM (x : CQ) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

/-- All fields and every nested array coordinate are retained by the existing
mapArray operation. This is not an abstract relation on the returned receiver. -/
def fromCtorWeights (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights) : Weights :=
  {variant := fromCtorVariant w.variant,
   factors := mapArray (mapArray (mapArray fromCtorQM)) w.factors,
   points := mapArray (mapArray fromCtorQM) w.points,
   extra := mapArray fromCtorQM w.extra}

def actualNewWeightsSlot (v : AspisR1FinishRelationCurrent.transport.Variant)
    (alpha : Array AspisR1FinishRelationCurrent.aspis_core.field.QM31 10#usize)
    (z : Array AspisR1FinishRelationCurrent.aspis_core.circle.SecureCirclePoint 2#usize) :
    Result (core.result.Result Weights AspisR1FinishRelationCurrent.verifier.Error) := do
  let r ← AspisR1S9ActualWeightsNewBoxNewV3.weights_new (toCtorVariant v)
    (mapArray toCtorQM alpha) (mapArray toCtorPoint z)
  ok (match r with | .Ok w => .Ok (fromCtorWeights w) | .Err .Allocation => .Err .Allocation)

def installActualConstructor {D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps Weights D) :
    AspisR1FinishRelationCurrent.FinishOps Weights D :=
  AspisR1S9FinishActualPairSlotV1.installActualPair {ops with newWeights := actualNewWeightsSlot}

/-- Slot acceptance supplies that same successful V3 constructor and the
complete structurally transported receiver, without an independent output
or variant-preservation assumption. -/
theorem actualNewWeightsSlot_success
    (v : AspisR1FinishRelationCurrent.transport.Variant)
    (alpha : Array AspisR1FinishRelationCurrent.aspis_core.field.QM31 10#usize)
    (z : Array AspisR1FinishRelationCurrent.aspis_core.circle.SecureCirclePoint 2#usize)
    (self : Weights) (h : actualNewWeightsSlot v alpha z = .ok (.Ok self)) :
    ∃ w, AspisR1S9ActualWeightsNewBoxNewV3.weights_new (toCtorVariant v)
      (mapArray toCtorQM alpha) (mapArray toCtorPoint z) = .ok (.Ok w) ∧ self = fromCtorWeights w := by
  unfold actualNewWeightsSlot at h
  cases hr : AspisR1S9ActualWeightsNewBoxNewV3.weights_new (toCtorVariant v)
      (mapArray toCtorQM alpha) (mapArray toCtorPoint z) with
  | fail e => simp only [hr,bind_tc_fail] at h; cases h
  | div => simp only [hr,bind_tc_div] at h; cases h
  | ok r =>
    simp only [hr,bind_tc_ok] at h
    cases r with
    | Err e => cases e; cases h
    | Ok w =>
      have he : fromCtorWeights w = self := core.result.Result.Ok.inj (Result.ok.inj h)
      exact ⟨w,rfl,he.symm⟩

theorem actualNewWeightsSlot_success_variant
    (v : AspisR1FinishRelationCurrent.transport.Variant)
    (alpha : Array AspisR1FinishRelationCurrent.aspis_core.field.QM31 10#usize)
    (z : Array AspisR1FinishRelationCurrent.aspis_core.circle.SecureCirclePoint 2#usize)
    (self : Weights) (h : actualNewWeightsSlot v alpha z = .ok (.Ok self)) :
    self.variant = fromCtorVariant (toCtorVariant v) := by
  obtain ⟨w,hw,hself⟩ := actualNewWeightsSlot_success v alpha z self h
  have hv := AspisR1S9ConstructorV3VariantPreservedV1.constructor_success_variant_preserved
    (toCtorVariant v) (mapArray toCtorQM alpha) (mapArray toCtorPoint z) w hw
  rw [hself]
  change fromCtorVariant w.variant = _
  rw [hv]

/-- S2 finish acceptance under BOTH concrete constructor and Pair slots now
supplies the same actual Pair receiver with its S2 variant PROVED. Source
normalization and Box/runtime correspondence of V3 remain explicit boundaries. -/
theorem finish_s2_success_reaches_s2_actual_pair {D : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps Weights D)
    (v : AspisR1FinishRelationCurrent.verifier.View) (p : AspisR1FinishRelationCurrent.verifier.Prepared)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hv : p.variant = AspisR1FinishRelationCurrent.transport.Variant.S2)
    (h : AspisR1FinishRelationCurrent.verifier.finish_relation (installActualConstructor ops)
      v p a obs = .ok (.Ok ())) :
    ∃ (self : Weights) (selected : Slice AspisR1S9FinishActualPairSlotV1.FW)
      (nativeOut : AspisR1S9FinishActualPairSlotV1.NW),
      actualNewWeightsSlot p.variant p.semantic_alpha p.z = .ok (.Ok self) ∧
      self.variant = AspisR1S9ProductionPairCutV1.transport.Variant.S2 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice AspisR1S9FinishActualPairSlotV1.FW))
        p.alpha { «end» := 2#usize } = .ok selected ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self
        (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
        (AspisR1S9FinishActualPairSlotV1.toNative p.kappa) = .ok (.Ok nativeOut) := by
  obtain ⟨self,selected,nativeOut,hnew,hselected,hpair⟩ :=
    AspisR1S9FinishActualPairSlotV1.finish_s2_success_reaches_actual_pair
      {ops with newWeights := actualNewWeightsSlot} v p a obs hv h
  have hself := actualNewWeightsSlot_success_variant p.variant p.semantic_alpha p.z self hnew
  rw [hv] at hself
  exact ⟨self,selected,nativeOut,hnew,hself,hselected,hpair⟩

#print axioms actualNewWeightsSlot_success
#print axioms actualNewWeightsSlot_success_variant
#print axioms finish_s2_success_reaches_s2_actual_pair
end AspisR1S9FinishActualConstructorSlotV1
