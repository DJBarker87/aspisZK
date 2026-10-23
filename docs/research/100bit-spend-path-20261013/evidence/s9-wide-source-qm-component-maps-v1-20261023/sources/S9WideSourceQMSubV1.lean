import AspisR1S9ActualWideMulCutV1.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9WideSourceCMMapV1
import S9WideSourceRecordMapV1
import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceQMSubV1

abbrev WideQM := AspisR1S9ActualWideMulCutV1.field.QM31
abbrev QCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31

def toQCM := AspisR1S9WideSourceCMMapV1.toQCM
def toQQM := AspisR1S9WideSourceRecordMapV1.toQQM
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutQMSub (x y : QQM) : Result QQM := do
  let c0 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub x.c0 y.c0
  let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub x.c1 y.c1
  ok ⟨c0, c1⟩

theorem shared_map_eq_cm_map {A B : Type} (f : A → B) :
    AspisR1S9SourceResultTransportV1.mapResult f =
      AspisR1S9WideSourceCMMapV1.mapResult f := by
  funext r
  cases r <;> rfl

/-- Same-call full-Result map for QM subtraction, using a function-head
conversion before rewriting the generated arithmetic call. -/
theorem qm_sub_maps (x y : WideQM) :
    mapResult toQQM (AspisR1S9ActualWideMulCutV1.field.QM31.sub x y) =
      qcutQMSub (toQQM x) (toQQM y) := by
  unfold AspisR1S9ActualWideMulCutV1.field.QM31.sub qcutQMSub
  change mapResult toQQM
      (do
        let c0 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c0 y.c0
        let c1 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c1 y.c1
        ok ({ c0 := c0, c1 := c1 } : WideQM)) =
    (do
      let c0 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c0) (toQCM y.c0)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c1) (toQCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : QQM))
  have hfirstCm := AspisR1S9WideSourceCMMapV1.cm_sub_maps x.c0 y.c0
  have hhead := shared_map_eq_cm_map toQCM
  have hfirst :
      AspisR1S9SourceResultTransportV1.mapResult toQCM
          (AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c0 y.c0) =
        AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c0) (toQCM y.c0) := by
    exact (congrArg (fun f => f
      (AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c0 y.c0)) hhead).trans hfirstCm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c0) (toQCM y.c0))
    (fun c0 => do
      let c1 ← AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c1 y.c1
      ok ({ c0 := c0, c1 := c1 } : WideQM))
    (fun c0 => do
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c1) (toQCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : QQM))
    hfirst
  intro c0
  have hsecondCm := AspisR1S9WideSourceCMMapV1.cm_sub_maps x.c1 y.c1
  have hsecond :
      AspisR1S9SourceResultTransportV1.mapResult toQCM
          (AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c1 y.c1) =
        AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c1) (toQCM y.c1) := by
    exact (congrArg (fun f => f
      (AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c1 y.c1)) hhead).trans hsecondCm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.sub x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c1) (toQCM y.c1))
    (fun c1 => ok ({ c0 := c0, c1 := c1 } : WideQM))
    (fun c1 => ok ({ c0 := toQCM c0, c1 := c1 } : QQM))
    hsecond
  intro c1
  rfl

#print axioms qm_sub_maps

end AspisR1S9WideSourceQMSubV1
