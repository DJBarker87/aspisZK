import S9ConstructorV3QMMulCanonicalV1
import S9WideSourceQMAddV1
import S9WideSourceQMSubV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3QMAddSubMapV1
abbrev S := AspisR1S9ConstructorV3QMMulCanonicalV1.SourceQM
abbrev Q := AspisR1S9ConstructorV3QMMulCanonicalV1.TargetQM
abbrev toQM := AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM
abbrev toCM := AspisR1S9ConstructorV3QMMulCanonicalV1.toActualCM
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r
private theorem shared_cm_map {A B : Type} (f : A → B) :
    AspisR1S9SourceResultTransportV1.mapResult f =
    AspisR1S9ConstructorV3QMMulMapV1.mapResult f := by
  funext r; cases r <;> rfl

theorem qm_add_maps (x y : S) :
    mapResult toQM (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add x y) =
      AspisR1S9WideSourceQMAddV1.qcutQMAdd (toQM x) (toQM y) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add
    AspisR1S9WideSourceQMAddV1.qcutQMAdd
  change mapResult toQM
      (do
        let c0 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 y.c0
        let c1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c1 y.c1
        ok ({ c0 := c0, c1 := c1 } : S)) =
    (do
      let c0 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toCM x.c0) (toCM y.c0)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toCM x.c1) (toCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : Q))
  have hfirst : mapResult toCM
      (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 y.c0) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toCM x.c0) (toCM y.c0) := by
    exact (congrArg (fun f => f
      (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 y.c0))
      (shared_cm_map toCM)).trans
        (AspisR1S9ConstructorV3QMMulMapV1.cm_add_map x.c0 y.c0)
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toCM toQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toCM x.c0) (toCM y.c0))
    (fun c0 => do
      let c1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c1 y.c1
      ok ({ c0 := c0, c1 := c1 } : S))
    (fun c0 => do
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toCM x.c1) (toCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : Q)) hfirst
  intro c0
  have hsecond : mapResult toCM
      (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c1 y.c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toCM x.c1) (toCM y.c1) := by
    exact (congrArg (fun f => f
      (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c1 y.c1))
      (shared_cm_map toCM)).trans
        (AspisR1S9ConstructorV3QMMulMapV1.cm_add_map x.c1 y.c1)
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toCM toQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toCM x.c1) (toCM y.c1))
    (fun c1 => ok ({ c0 := c0, c1 := c1 } : S))
    (fun c1 => ok ({ c0 := toCM c0, c1 := c1 } : Q)) hsecond
  intro c1
  rfl
#print axioms qm_add_maps

theorem qm_sub_maps (x y : S) :
    mapResult toQM (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub x y) =
      AspisR1S9WideSourceQMSubV1.qcutQMSub (toQM x) (toQM y) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub
    AspisR1S9WideSourceQMSubV1.qcutQMSub
  change mapResult toQM
      (do
        let c0 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c0 y.c0
        let c1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c1 y.c1
        ok ({ c0 := c0, c1 := c1 } : S)) =
    (do
      let c0 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toCM x.c0) (toCM y.c0)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toCM x.c1) (toCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : Q))
  have hfirst : mapResult toCM
      (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c0 y.c0) =
      AspisR1S9ActualQMMulCutV1.field.CM31.sub (toCM x.c0) (toCM y.c0) := by
    exact (congrArg (fun f => f
      (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c0 y.c0))
      (shared_cm_map toCM)).trans
        (AspisR1S9ConstructorV3QMMulMapV1.cm_sub_map x.c0 y.c0)
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toCM toQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toCM x.c0) (toCM y.c0))
    (fun c0 => do
      let c1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c1 y.c1
      ok ({ c0 := c0, c1 := c1 } : S))
    (fun c0 => do
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toCM x.c1) (toCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : Q)) hfirst
  intro c0
  have hsecond : mapResult toCM
      (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c1 y.c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.sub (toCM x.c1) (toCM y.c1) := by
    exact (congrArg (fun f => f
      (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c1 y.c1))
      (shared_cm_map toCM)).trans
        (AspisR1S9ConstructorV3QMMulMapV1.cm_sub_map x.c1 y.c1)
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toCM toQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toCM x.c1) (toCM y.c1))
    (fun c1 => ok ({ c0 := c0, c1 := c1 } : S))
    (fun c1 => ok ({ c0 := toCM c0, c1 := c1 } : Q)) hsecond
  intro c1
  rfl
#print axioms qm_sub_maps

end AspisR1S9ConstructorV3QMAddSubMapV1
