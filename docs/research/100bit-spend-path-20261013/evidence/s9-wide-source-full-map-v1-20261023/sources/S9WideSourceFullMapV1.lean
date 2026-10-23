import AspisR1S9ActualWideMulCutV1.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9WideSourceQMAddV1
import S9WideSourceQMSubV1
import S9WideSourceQMMulMapV1
import S9WideSourceRecordMapV1
import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceFullMapV1

abbrev WideQM := AspisR1S9ActualWideMulCutV1.field.QM31
abbrev WideExact := AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact
abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31

def toQQM := AspisR1S9WideSourceRecordMapV1.toQQM
def toQWide (x : WideExact) : QQM × QQM := (toQQM x.c0, toQQM x.c1)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutWideMulFormula (x y : QQM × QQM) : Result (QQM × QQM) := do
  let ac ← AspisR1S9ActualQMMulCutV1.field.QM31.mul x.1 y.1
  let bd ← AspisR1S9ActualQMMulCutV1.field.QM31.mul x.2 y.2
  let q ← AspisR1S9WideSourceQMAddV1.qcutQMAdd x.1 x.2
  let q1 ← AspisR1S9WideSourceQMAddV1.qcutQMAdd y.1 y.2
  let cross ← AspisR1S9ActualQMMulCutV1.field.QM31.mul q q1
  let q2 ← AspisR1S9WideSourceRecordMapV1.qcutMulUFormula bd
  let q3 ← AspisR1S9WideSourceQMAddV1.qcutQMAdd ac q2
  let q4 ← AspisR1S9WideSourceQMSubV1.qcutQMSub cross ac
  let q5 ← AspisR1S9WideSourceQMSubV1.qcutQMSub q4 bd
  ok (q3, q5)

/-- Complete same-call Result map of the transparent WideExact.mul body into
its actual QMMul-cut operation cone. The map preserves fail/divergence; checked
CurrentWide refinement is a separate canonical-input boundary. -/
theorem wide_mul_maps_to_qcut_formula (x y : WideExact) :
    mapResult toQWide
      (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) =
      qcutWideMulFormula (toQWide x) (toQWide y) := by
  unfold AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul
    qcutWideMulFormula
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9WideSourceQMMulMapV1.qm_mul_maps x.c0 y.c0)
  intro ac
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9WideSourceQMMulMapV1.qm_mul_maps x.c1 y.c1)
  intro bd
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9WideSourceQMAddV1.qm_add_maps x.c0 x.c1)
  intro q
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9WideSourceQMAddV1.qm_add_maps y.c0 y.c1)
  intro q1
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9WideSourceQMMulMapV1.qm_mul_maps q q1)
  intro cross
  have hshared_record_map {A B : Type} (f : A → B) :
      AspisR1S9SourceResultTransportV1.mapResult f =
        AspisR1S9WideSourceRecordMapV1.mapResult f := by
    funext r
    cases r <;> rfl
  have hmul_u_record :=
    AspisR1S9WideSourceRecordMapV1.wide_mul_u_maps_to_qcut_formula bd
  have hmul_u :
      mapResult toQQM (AspisR1S9ActualWideMulCutV1.field.wide_exact.mul_u bd) =
        AspisR1S9WideSourceRecordMapV1.qcutMulUFormula (toQQM bd) :=
    (congrArg (fun f => f (AspisR1S9ActualWideMulCutV1.field.wide_exact.mul_u bd))
      (hshared_record_map toQQM)).trans hmul_u_record
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _ hmul_u
  intro q2
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9WideSourceQMAddV1.qm_add_maps ac q2)
  intro q3
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9WideSourceQMSubV1.qm_sub_maps cross ac)
  intro q4
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9WideSourceQMSubV1.qm_sub_maps q4 bd)
  intro q5
  rfl

#print axioms wide_mul_maps_to_qcut_formula

end AspisR1S9WideSourceFullMapV1
