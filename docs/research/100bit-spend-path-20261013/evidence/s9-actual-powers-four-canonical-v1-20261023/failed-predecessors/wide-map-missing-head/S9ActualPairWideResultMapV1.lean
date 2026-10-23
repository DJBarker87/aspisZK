import S9PairSourceQMMulCanonicalV1
import S9WideSourceQMAddV1
import S9WideSourceQMSubV1
import S9WideSourceRecordMapV1
import S9WideSourceFullMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualPairQMAddMapV1

abbrev WideQM := AspisR1S9ProductionPairCutV1.aspis_core.field.QM31
abbrev QCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31

def toQCM := AspisR1S9PairSourceQMMulMapV1.toActualCM
def toQQM := AspisR1S9PairSourceQMMulCanonicalV1.toActualQM
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

abbrev qcutQMAdd := AspisR1S9WideSourceQMAddV1.qcutQMAdd

/-- Isolated same-call Result map for QM addition. Both source CM binds map to
the actual QMMul-cut CM operations; failures and divergence are preserved. -/
theorem qm_add_maps (x y : WideQM) :
    mapResult toQQM (AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.add x y) =
      qcutQMAdd (toQQM x) (toQQM y) := by
  unfold AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.add qcutQMAdd
  change mapResult toQQM
      (do
        let c0 ← AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.add x.c0 y.c0
        let c1 ← AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.add x.c1 y.c1
        ok ({ c0 := c0, c1 := c1 } : WideQM)) =
    (do
      let c0 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM y.c0)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c1) (toQCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : QQM))
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQCM toQQM
    (AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.add x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c0) (toQCM y.c0))
    (fun c0 => do
      let c1 ← AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.add x.c1 y.c1
      ok ({ c0 := c0, c1 := c1 } : WideQM))
    (fun c0 => do
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c1) (toQCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : QQM))
    (AspisR1S9PairSourceQMMulMapV1.cm_add_map x.c0 y.c0)
  intro c0
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQCM toQQM
    (AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.add x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (toQCM x.c1) (toQCM y.c1))
    (fun c1 => ok ({ c0 := c0, c1 := c1 } : WideQM))
    (fun c1 => ok ({ c0 := toQCM c0, c1 := c1 } : QQM))
    (AspisR1S9PairSourceQMMulMapV1.cm_add_map x.c1 y.c1)
  intro c1
  rfl

#print axioms qm_add_maps

end AspisR1S9ActualPairQMAddMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualPairQMSubMapV1

abbrev WideQM := AspisR1S9ProductionPairCutV1.aspis_core.field.QM31
abbrev QCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31

def toQCM := AspisR1S9PairSourceQMMulMapV1.toActualCM
def toQQM := AspisR1S9PairSourceQMMulCanonicalV1.toActualQM
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

abbrev qcutQMSub := AspisR1S9WideSourceQMSubV1.qcutQMSub

/-- Same-call full-Result map for QM subtraction, using a function-head
conversion before rewriting the generated arithmetic call. -/
theorem qm_sub_maps (x y : WideQM) :
    mapResult toQQM (AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.sub x y) =
      qcutQMSub (toQQM x) (toQQM y) := by
  unfold AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.sub qcutQMSub
  change mapResult toQQM
      (do
        let c0 ← AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c0 y.c0
        let c1 ← AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c1 y.c1
        ok ({ c0 := c0, c1 := c1 } : WideQM)) =
    (do
      let c0 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c0) (toQCM y.c0)
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c1) (toQCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : QQM))
  have hfirstCm := AspisR1S9PairSourceQMMulMapV1.cm_sub_map x.c0 y.c0
  have hhead := shared_map_eq_cm_map toQCM
  have hfirst :
      AspisR1S9SourceResultTransportV1.mapResult toQCM
          (AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c0 y.c0) =
        AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c0) (toQCM y.c0) := by
    exact (congrArg (fun f => f
      (AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c0 y.c0)) hhead).trans hfirstCm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQCM toQQM
    (AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c0) (toQCM y.c0))
    (fun c0 => do
      let c1 ← AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c1 y.c1
      ok ({ c0 := c0, c1 := c1 } : WideQM))
    (fun c0 => do
      let c1 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c1) (toQCM y.c1)
      ok ({ c0 := c0, c1 := c1 } : QQM))
    hfirst
  intro c0
  have hsecondCm := AspisR1S9PairSourceQMMulMapV1.cm_sub_map x.c1 y.c1
  have hsecond :
      AspisR1S9SourceResultTransportV1.mapResult toQCM
          (AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c1 y.c1) =
        AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c1) (toQCM y.c1) := by
    exact (congrArg (fun f => f
      (AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c1 y.c1)) hhead).trans hsecondCm
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQCM toQQM
    (AspisR1S9ProductionPairCutV1.aspis_core.field.CM31.sub x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (toQCM x.c1) (toQCM y.c1))
    (fun c1 => ok ({ c0 := c0, c1 := c1 } : WideQM))
    (fun c1 => ok ({ c0 := toQCM c0, c1 := c1 } : QQM))
    hsecond
  intro c1
  rfl

#print axioms qm_sub_maps

end AspisR1S9ActualPairQMSubMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualPairWideResultMapV1

abbrev WideQM := AspisR1S9ProductionPairCutV1.aspis_core.field.QM31
abbrev WideExact := AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact
abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31

def toQQM := AspisR1S9PairSourceQMMulCanonicalV1.toActualQM
def toQWide (x : WideExact) : QQM × QQM := (toQQM x.c0, toQQM x.c1)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

abbrev qcutWideMulFormula := AspisR1S9WideSourceFullMapV1.qcutWideMulFormula

private theorem mapResult_bind_local {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) : mapResult f (Bind.bind r k) =
      Bind.bind r (fun x => mapResult f (k x)) := by
  cases r <;> rfl

private theorem wide_mul_u_map (x : WideQM) :
    mapResult toQQM (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.mul_u x) =
      AspisR1S9WideSourceRecordMapV1.qcutMulUFormula (toQQM x) := by
  unfold AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.mul_u
    AspisR1S9WideSourceRecordMapV1.qcutMulUFormula
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    AspisR1S9PairSourceQMMulMapV1.toActualCM toQQM _ _ _ _
    (AspisR1S9PairSourceQMMulCanonicalV1.mul_by_r_map x.c1)
  intro c
  rfl

/-- Complete same-call Result map of the transparent WideExact.mul body into
its actual QMMul-cut operation cone. The map preserves fail/divergence; checked
CurrentWide refinement is a separate canonical-input boundary. -/
theorem wide_mul_maps_to_qcut_formula (x y : WideExact) :
    mapResult toQWide
      (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul x y) =
      qcutWideMulFormula (toQWide x) (toQWide y) := by
  unfold AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul
    qcutWideMulFormula
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9PairSourceQMMulCanonicalV1.qm_mul_maps x.c0 y.c0)
  intro ac
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9PairSourceQMMulCanonicalV1.qm_mul_maps x.c1 y.c1)
  intro bd
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9ActualPairQMAddMapV1.qm_add_maps x.c0 x.c1)
  intro q
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9ActualPairQMAddMapV1.qm_add_maps y.c0 y.c1)
  intro q1
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9PairSourceQMMulCanonicalV1.qm_mul_maps q q1)
  intro cross
  have hmul_u := wide_mul_u_map bd
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _ hmul_u
  intro q2
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9ActualPairQMAddMapV1.qm_add_maps ac q2)
  intro q3
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9ActualPairQMSubMapV1.qm_sub_maps cross ac)
  intro q4
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq
    toQQM toQWide _ _ _ _
    (AspisR1S9ActualPairQMSubMapV1.qm_sub_maps q4 bd)
  intro q5
  rfl

#print axioms wide_mul_maps_to_qcut_formula

end AspisR1S9ActualPairWideResultMapV1
