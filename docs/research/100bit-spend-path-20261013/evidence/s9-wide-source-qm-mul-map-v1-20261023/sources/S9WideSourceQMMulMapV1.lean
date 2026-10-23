import AspisR1S9ActualWideMulCutV1.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9WideSourceCMMapV1
import S9WideSourceRecordMapV1
import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceQMMulMapV1

abbrev WideQM := AspisR1S9ActualWideMulCutV1.field.QM31
abbrev WideCM := AspisR1S9ActualWideMulCutV1.field.CM31
abbrev QCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31

def toQCM := AspisR1S9WideSourceCMMapV1.toQCM
def toQQM := AspisR1S9WideSourceRecordMapV1.toQQM
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

theorem shared_map_eq_cm_map {A B : Type} (f : A → B) :
    AspisR1S9SourceResultTransportV1.mapResult f =
      AspisR1S9WideSourceCMMapV1.mapResult f := by
  funext r
  cases r <;> rfl

theorem shared_map_eq_record_map {A B : Type} (f : A → B) :
    AspisR1S9SourceResultTransportV1.mapResult f =
      AspisR1S9WideSourceRecordMapV1.mapResult f := by
  funext r
  cases r <;> rfl

/-- Same-call full-Result map for all binds in the transparent source QM.mul
body to the corresponding operation in the actual QMMul cut. Each CM/record
map is converted at the function head before being applied to generated ops. -/
theorem qm_mul_maps (x y : WideQM) :
    mapResult toQQM (AspisR1S9ActualWideMulCutV1.field.QM31.mul x y) =
      AspisR1S9ActualQMMulCutV1.field.QM31.mul (toQQM x) (toQQM y) := by
  unfold AspisR1S9ActualWideMulCutV1.field.QM31.mul
    AspisR1S9ActualQMMulCutV1.field.QM31.mul
  change mapResult toQQM
      (do
        let m0 ← AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c0 y.c0
        let m1 ← AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c1 y.c1
        let c ← AspisR1S9ActualWideMulCutV1.field.CM31.add x.c0 x.c1
        let c1 ← AspisR1S9ActualWideMulCutV1.field.CM31.add y.c0 y.c1
        let m2 ← AspisR1S9ActualWideMulCutV1.field.CM31.mul c c1
        let c2 ← AspisR1S9ActualWideMulCutV1.field.mul_by_r m1
        let c3 ← AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2
        let c4 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0
        let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
        ok ({ c0 := c3, c1 := c5 } : WideQM)) =
    (do
      let m0 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM x.c0) (toQCM y.c0)
      let m1 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM x.c1) (toQCM y.c1)
      let c ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM x.c1)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM y.c0) (toQCM y.c1)
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : QQM))
  have hmap := shared_map_eq_cm_map toQCM
  have hrecord := shared_map_eq_record_map toQCM
  have h0cm := AspisR1S9WideSourceCMMapV1.cm_mul_maps x.c0 y.c0
  have h0 : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c0 y.c0) =
      AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM x.c0) (toQCM y.c0) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c0 y.c0)) hmap).trans h0cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM x.c0) (toQCM y.c0))
    (fun m0 => do
      let m1 ← AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c1 y.c1
      let c ← AspisR1S9ActualWideMulCutV1.field.CM31.add x.c0 x.c1
      let c1 ← AspisR1S9ActualWideMulCutV1.field.CM31.add y.c0 y.c1
      let m2 ← AspisR1S9ActualWideMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualWideMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun m0 => do
      let m1 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM x.c1) (toQCM y.c1)
      let c ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM x.c1)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM y.c0) (toQCM y.c1)
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : QQM)) h0
  intro m0
  have h1cm := AspisR1S9WideSourceCMMapV1.cm_mul_maps x.c1 y.c1
  have h1 : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c1 y.c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM x.c1) (toQCM y.c1) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c1 y.c1)) hmap).trans h1cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.mul x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM x.c1) (toQCM y.c1))
    (fun m1 => do
      let c ← AspisR1S9ActualWideMulCutV1.field.CM31.add x.c0 x.c1
      let c1 ← AspisR1S9ActualWideMulCutV1.field.CM31.add y.c0 y.c1
      let m2 ← AspisR1S9ActualWideMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualWideMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun m1 => do
      let c ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM x.c1)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM y.c0) (toQCM y.c1)
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 (toQCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : QQM)) h1
  intro m1
  have ha0cm := AspisR1S9WideSourceCMMapV1.cm_add_maps x.c0 x.c1
  have ha0 : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.add x.c0 x.c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM x.c1) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.CM31.add x.c0 x.c1)) hmap).trans ha0cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.add x.c0 x.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM x.c1))
    (fun c => do
      let c1 ← AspisR1S9ActualWideMulCutV1.field.CM31.add y.c0 y.c1
      let m2 ← AspisR1S9ActualWideMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualWideMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun c => do
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM y.c0) (toQCM y.c1)
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (toQCM m1)
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 (toQCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toQCM m1)
      ok ({ c0 := c3, c1 := c5 } : QQM)) ha0
  intro c
  have ha1cm := AspisR1S9WideSourceCMMapV1.cm_add_maps y.c0 y.c1
  have ha1 : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.add y.c0 y.c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM y.c0) (toQCM y.c1) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.CM31.add y.c0 y.c1)) hmap).trans ha1cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.add y.c0 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM y.c0) (toQCM y.c1))
    (fun c1 => do
      let m2 ← AspisR1S9ActualWideMulCutV1.field.CM31.mul c c1
      let c2 ← AspisR1S9ActualWideMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun c1 => do
      let m2 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM c) c1
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (toQCM m1)
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 (toQCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toQCM m1)
      ok ({ c0 := c3, c1 := c5 } : QQM)) ha1
  intro c1
  have hm2cm := AspisR1S9WideSourceCMMapV1.cm_mul_maps c c1
  have hm2 : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.mul c c1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM c) (toQCM c1) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.CM31.mul c c1)) hmap).trans hm2cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.mul c c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (toQCM c) (toQCM c1))
    (fun m2 => do
      let c2 ← AspisR1S9ActualWideMulCutV1.field.mul_by_r m1
      let c3 ← AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun m2 => do
      let c2 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (toQCM m1)
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub m2 (toQCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toQCM m1)
      ok ({ c0 := c3, c1 := c5 } : QQM)) hm2
  intro m2
  have hr := AspisR1S9WideSourceRecordMapV1.wide_mul_by_r_maps_to_qcut m1
  have hr' : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.mul_by_r m1) =
      AspisR1S9ActualQMMulCutV1.field.mul_by_r (toQCM m1) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.mul_by_r m1)) hrecord).trans hr
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.mul_by_r m1)
    (AspisR1S9ActualQMMulCutV1.field.mul_by_r (toQCM m1))
    (fun c2 => do
      let c3 ← AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2
      let c4 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun c2 => do
      let c3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM m0) c2
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM m2) (toQCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toQCM m1)
      ok ({ c0 := c3, c1 := c5 } : QQM)) hr'
  intro c2
  have ha2cm := AspisR1S9WideSourceCMMapV1.cm_add_maps m0 c2
  have ha2 : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2) =
      AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM m0) (toQCM c2) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2)) hmap).trans ha2cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.add m0 c2)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM m0) (toQCM c2))
    (fun c3 => do
      let c4 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0
      let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun c3 => do
      let c4 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM m2) (toQCM m0)
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toQCM m1)
      ok ({ c0 := c3, c1 := c5 } : QQM)) ha2
  intro c3
  have hs0cm := AspisR1S9WideSourceCMMapV1.cm_sub_maps m2 m0
  have hs0 : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0) =
      AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM m2) (toQCM m0) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0)) hmap).trans hs0cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.sub m2 m0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM m2) (toQCM m0))
    (fun c4 => do
      let c5 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1
      ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun c4 => do
      let c5 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub c4 (toQCM m1)
      ok ({ c0 := toQCM c3, c1 := c5 } : QQM)) hs0
  intro c4
  have hs1cm := AspisR1S9WideSourceCMMapV1.cm_sub_maps c4 m1
  have hs1 : mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1) =
      AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM c4) (toQCM m1) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1)) hmap).trans hs1cm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.sub c4 m1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM c4) (toQCM m1))
    (fun c5 => ok ({ c0 := c3, c1 := c5 } : WideQM))
    (fun c5 => ok ({ c0 := toQCM c3, c1 := c5 } : QQM)) hs1
  intro c5
  rfl

#print axioms qm_mul_maps

end AspisR1S9WideSourceQMMulMapV1
