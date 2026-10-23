import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9ConstructorV3QMMulMapV1
import S9SourceResultTransportV1
import S9ActualQM31WrappingMapV1
import S9ActualQM31TotalCanonicalV1
import R22CanonicalQM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConstructorV3QMMulCanonicalV1

abbrev SourceQM := AspisR1S9ActualWeightsNewBoxNewV3.field.QM31
abbrev TargetQM := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev SourceCM := AspisR1S9ActualWeightsNewBoxNewV3.field.CM31
abbrev TargetCM := AspisR1S9ActualQMMulCutV1.field.CM31

abbrev toActualCM := AspisR1S9ConstructorV3QMMulMapV1.toActualCM

def toActualQM (x : SourceQM) : TargetQM :=
  ⟨toActualCM x.c0, toActualCM x.c1⟩

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

private theorem shared_map_eq_cm_map {A B : Type} (f : A → B) :
    AspisR1S9SourceResultTransportV1.mapResult f =
      AspisR1S9ConstructorV3QMMulMapV1.mapResult f := by
  funext r
  cases r <;> rfl

private theorem shared_map_eq_record_map {A B : Type} (f : A → B) :
    AspisR1S9SourceResultTransportV1.mapResult f =
      AspisR1S9ConstructorV3QMMulMapV1.mapResult f := by
  funext r
  cases r <;> rfl

private theorem mapResult_bind_local {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) : mapResult f (Bind.bind r k) =
      Bind.bind r (fun x => mapResult f (k x)) := by
  cases r <;> rfl

private theorem mapResult_ok {A B : Type} (f : A → B) (x : A) :
    mapResult f (.ok x) = .ok (f x) := rfl

theorem mul_by_r_map (x : SourceCM) :
    mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r x) =
      AspisR1S9ActualQMMulCutV1.field.mul_by_r (toActualCM x) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r
    AspisR1S9ActualQMMulCutV1.field.mul_by_r
  simp only [mapResult_bind_local,
    AspisR1S9ConstructorV3QMMulMapV1.m31_double_same,
    AspisR1S9ConstructorV3QMMulMapV1.m31_add_same,
    AspisR1S9ConstructorV3QMMulMapV1.m31_sub_same,
    mapResult_ok, toActualCM, AspisR1S9ConstructorV3QMMulMapV1.toActualCM]

/-- Same-call full-Result map for all binds in the transparent source QM.mul
body to the corresponding operation in the actual QMMul cut. Each CM/record
map is converted at the function head before being applied to generated ops. -/
theorem qm_mul_maps (x y : SourceQM) :
    mapResult toActualQM (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x y) =
      AspisR1S9ActualQMMulCutV1.field.QM31.mul (toActualQM x) (toActualQM y) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul
    AspisR1S9ActualQMMulCutV1.field.QM31.mul
  change mapResult toActualQM
      (do
        let m0 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c0 y.c0
        let m1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c1 y.c1
        let c ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 x.c1
        let c1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add y.c0 y.c1
        let m2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul c c1
        let c2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1
        let c3 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2
        let c4 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0
        let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
        ok ({ c0 := c3, c1 := c5 } : SourceQM)) =
    (do
      let m0 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM x.c0) (toActualCM y.c0)
      let m1 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM x.c1) (toActualCM y.c1)
      let c ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM x.c0) (toActualCM x.c1)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM y.c0) (toActualCM y.c1)
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : TargetQM))
  have hmap := shared_map_eq_cm_map toActualCM
  have hrecord := shared_map_eq_record_map toActualCM
  have h0cm := AspisR1S9ConstructorV3QMMulMapV1.cm_mul_map x.c0 y.c0
  have h0 : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c0 y.c0) =
      AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM x.c0) (toActualCM y.c0) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c0 y.c0)) hmap).trans h0cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM x.c0) (toActualCM y.c0))
    (fun m0 => do
      let m1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c1 y.c1
      let c ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 x.c1
      let c1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add y.c0 y.c1
      let m2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun m0 => do
      let m1 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM x.c1) (toActualCM y.c1)
      let c ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM x.c0) (toActualCM x.c1)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM y.c0) (toActualCM y.c1)
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : TargetQM)) h0
  intro m0
  have h1cm := AspisR1S9ConstructorV3QMMulMapV1.cm_mul_map x.c1 y.c1
  have h1 : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c1 y.c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM x.c1) (toActualCM y.c1) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c1 y.c1)) hmap).trans h1cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM x.c1) (toActualCM y.c1))
    (fun m1 => do
      let c ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 x.c1
      let c1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add y.c0 y.c1
      let m2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun m1 => do
      let c ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM x.c0) (toActualCM x.c1)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM y.c0) (toActualCM y.c1)
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 (toActualCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : TargetQM)) h1
  intro m1
  have ha0cm := AspisR1S9ConstructorV3QMMulMapV1.cm_add_map x.c0 x.c1
  have ha0 : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 x.c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM x.c0) (toActualCM x.c1) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 x.c1)) hmap).trans ha0cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add x.c0 x.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM x.c0) (toActualCM x.c1))
    (fun c => do
      let c1 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add y.c0 y.c1
      let m2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun c => do
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM y.c0) (toActualCM y.c1)
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (toActualCM m1)
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 (toActualCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toActualCM m1)
      ok ({ c0 := c3, c1 := c5 } : TargetQM)) ha0
  intro c
  have ha1cm := AspisR1S9ConstructorV3QMMulMapV1.cm_add_map y.c0 y.c1
  have ha1 : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add y.c0 y.c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM y.c0) (toActualCM y.c1) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add y.c0 y.c1)) hmap).trans ha1cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add y.c0 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM y.c0) (toActualCM y.c1))
    (fun c1 => do
      let m2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun c1 => do
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM c) c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (toActualCM m1)
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 (toActualCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toActualCM m1)
      ok ({ c0 := c3, c1 := c5 } : TargetQM)) ha1
  intro c1
  have hm2cm := AspisR1S9ConstructorV3QMMulMapV1.cm_mul_map c c1
  have hm2 : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul c c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM c) (toActualCM c1) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul c c1)) hmap).trans hm2cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.mul c c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (toActualCM c) (toActualCM c1))
    (fun m2 => do
      let c2 ← AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun m2 => do
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (toActualCM m1)
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 (toActualCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toActualCM m1)
      ok ({ c0 := c3, c1 := c5 } : TargetQM)) hm2
  intro m2
  have hr := mul_by_r_map m1
  have hr' : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1) =
      AspisR1S9ActualQMMulCutV1.field.mul_by_r (toActualCM m1) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1)) hrecord).trans hr
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.mul_by_r m1)
    (AspisR1S9ActualQMMulCutV1.field.mul_by_r (toActualCM m1))
    (fun c2 => do
      let c3 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun c2 => do
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toActualCM m2) (toActualCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toActualCM m1)
      ok ({ c0 := c3, c1 := c5 } : TargetQM)) hr'
  intro c2
  have ha2cm := AspisR1S9ConstructorV3QMMulMapV1.cm_add_map m0 c2
  have ha2 : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM m0) (toActualCM c2) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2)) hmap).trans ha2cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.add m0 c2)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toActualCM m0) (toActualCM c2))
    (fun c3 => do
      let c4 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun c3 => do
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toActualCM m2) (toActualCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toActualCM m1)
      ok ({ c0 := c3, c1 := c5 } : TargetQM)) ha2
  intro c3
  have hs0cm := AspisR1S9ConstructorV3QMMulMapV1.cm_sub_map m2 m0
  have hs0 : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0) =
      AspisR1S9ActualQMMulCutV1.field.CM31.sub (toActualCM m2) (toActualCM m0) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0)) hmap).trans hs0cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub m2 m0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toActualCM m2) (toActualCM m0))
    (fun c4 => do
      let c5 ← AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun c4 => do
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toActualCM m1)
      ok ({ c0 := toActualCM c3, c1 := c5 } : TargetQM)) hs0
  intro c4
  have hs1cm := AspisR1S9ConstructorV3QMMulMapV1.cm_sub_map c4 m1
  have hs1 : mapResult toActualCM (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.sub (toActualCM c4) (toActualCM m1) :=
    (congrArg (fun f => f (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1)) hmap).trans hs1cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toActualCM toActualQM
    (AspisR1S9ActualWeightsNewBoxNewV3.field.CM31.sub c4 m1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toActualCM c4) (toActualCM m1))
    (fun c5 => ok ({ c0 := c3, c1 := c5 } : SourceQM))
    (fun c5 => ok ({ c0 := toActualCM c3, c1 := c5 } : TargetQM)) hs1
  intro c5
  rfl


#print axioms mul_by_r_map
#print axioms qm_mul_maps


def toProbe (x : SourceQM) : AspisR1S9ActualQM31WrappingMapV1.ProbeQM :=
  AspisR1S9ActualQM31WrappingMapV1.toProbeQM (toActualQM x)

theorem generated_mul_maps_to_cut (x y : SourceQM) :
    mapResult toActualQM
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x y) =
      AspisR1S9ActualQMMulCutV1.field.QM31.mul (toActualQM x) (toActualQM y) :=
  qm_mul_maps x y

theorem generated_mul_success_canonical
    (x y z : SourceQM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbe y))
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x y = .ok z) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbe z) := by
  have hcut : AspisR1S9ActualQMMulCutV1.field.QM31.mul (toActualQM x) (toActualQM y) =
      .ok (toActualQM z) := by
    have hm := generated_mul_maps_to_cut x y
    rw [hcall] at hm
    simp only [mapResult_ok] at hm
    exact hm.symm
  obtain ⟨out, hout, hcan⟩ :=
    AspisR1S9ActualQM31TotalCanonicalV1.actual_qm_mul_total_canonical
      (toActualQM x) (toActualQM y) hx hy
  have hout_eq : out = toActualQM z := Result.ok.inj (hout.symm.trans hcut)
  rw [hout_eq] at hcan
  simpa only [toProbe, AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
    toActualQM, toActualCM] using hcan

#print axioms generated_mul_maps_to_cut
#print axioms generated_mul_success_canonical

end AspisR1S9ConstructorV3QMMulCanonicalV1
