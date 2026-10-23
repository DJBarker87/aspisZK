import AspisR1S9ActualWideMulCutV1.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9WideSourceCMMapV1
import S9WideSourceRecordMapV1
import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceQMAddV1

abbrev WideQM := AspisR1S9ActualWideMulCutV1.field.QM31
abbrev QCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31

def toQCM := AspisR1S9WideSourceCMMapV1.toQCM
def toQQM := AspisR1S9WideSourceRecordMapV1.toQQM
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutQMAdd (x y : QQM) : Result QQM := do
  let c0 ← AspisR1S9ActualQMMulCutV1.field.CM31.add x.c0 y.c0
  let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add x.c1 y.c1
  ok ⟨c0, c1⟩

/-- Isolated same-call Result map for QM addition. Both source CM binds map to
the actual QMMul-cut CM operations; failures and divergence are preserved. -/
theorem qm_add_maps (x y : WideQM) :
    mapResult toQQM (AspisR1S9ActualWideMulCutV1.field.QM31.add x y) =
      qcutQMAdd (toQQM x) (toQQM y) := by
  unfold AspisR1S9ActualWideMulCutV1.field.QM31.add qcutQMAdd
  change mapResult toQQM
      (do
        let c0 ← AspisR1S9ActualWideMulCutV1.field.CM31.add x.c0 y.c0
        let c1 ← AspisR1S9ActualWideMulCutV1.field.CM31.add x.c1 y.c1
        ok ({ c0 := c0, c1 := c1 } : WideQM)) =
    (do
      let c0 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM y.c0)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c1) (toQCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : QQM))
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.add x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM y.c0))
    (fun c0 => do
      let c1 ← AspisR1S9ActualWideMulCutV1.field.CM31.add x.c1 y.c1
      ok ({ c0 := c0, c1 := c1 } : WideQM))
    (fun c0 => do
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c1) (toQCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : QQM))
    (AspisR1S9WideSourceCMMapV1.cm_add_maps x.c0 y.c0)
  intro c0
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQCM toQQM
    (AspisR1S9ActualWideMulCutV1.field.CM31.add x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c1) (toQCM y.c1))
    (fun c1 => ok ({ c0 := c0, c1 := c1 } : WideQM))
    (fun c1 => ok ({ c0 := toQCM c0, c1 := c1 } : QQM))
    (AspisR1S9WideSourceCMMapV1.cm_add_maps x.c1 y.c1)
  intro c1
  rfl

#print axioms qm_add_maps

end AspisR1S9WideSourceQMAddV1
