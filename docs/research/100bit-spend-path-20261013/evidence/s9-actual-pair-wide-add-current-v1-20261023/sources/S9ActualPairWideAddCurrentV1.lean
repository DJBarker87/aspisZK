import S9ActualPairWideCanonicalV1
import S9WideSourceQMCurrentOpsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualPairWideAddCurrentV1
open AspisR1S9ActualPairWideCanonicalV1
abbrev Q := AspisR1S9ProductionPairCutV1.aspis_core.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31
abbrev toQQM := AspisR1S9ActualPairQMAddMapV1.toQQM
abbrev toC (q : Q) : C := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent (toQQM q)
abbrev CanQ (q : Q) := AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
  (AspisR1S9ActualQM31WrappingMapV1.toProbeQM (toQQM q))

/-- Reuses the checked wrapping-to-current addition theorem; no fresh field
algebra, output contract, or success premise is introduced. -/
theorem qm_add_maps_current (x y : Q) (hx : CanQ x) (hy : CanQ y) :
    mapResult toC (AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.add x y) =
      AspisR1CurrentWide.field.QM31.add (toC x) (toC y) := by
  have hsource := AspisR1S9ActualPairQMAddMapV1.qm_add_maps x y
  have htarget := AspisR1S9WideSourceQMCurrentOpsV1.qcut_qm_add_maps_to_current
    (toQQM x) (toQQM y) hx hy
  calc
    _ = mapResult AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent
      (mapResult toQQM (AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.add x y)) := by
        cases AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.add x y <;> rfl
    _ = _ := (congrArg (mapResult AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent) hsource).trans htarget

/-- Full Result transport for actual Pair Wide addition, preserving errors
and divergence, under the existing canonical-input arithmetic guard. -/
theorem actual_wide_add_maps_current (x y : W) (hx : Canonical x) (hy : Canonical y) :
    mapResult toCurrent (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.add x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.add (toCurrent x) (toCurrent y) := by
  unfold AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.add
    AspisR1CurrentWide.field.wide_exact.WideExact.add
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toC toCurrent
    (AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.add x.c0 y.c0)
    (AspisR1CurrentWide.field.QM31.add (toC x.c0) (toC y.c0))
    (fun c0 => do
      let c1 ← AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.add x.c1 y.c1
      ok ({c0 := c0,c1 := c1} : W))
    (fun c0 => do
      let c1 ← AspisR1CurrentWide.field.QM31.add (toC x.c1) (toC y.c1)
      ok ({c0 := c0,c1 := c1} : CW))
    (qm_add_maps_current x.c0 y.c0 hx.1 hy.1)
  intro c0
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toC toCurrent
    (AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.add x.c1 y.c1)
    (AspisR1CurrentWide.field.QM31.add (toC x.c1) (toC y.c1))
    (fun c1 => ok ({c0 := c0,c1 := c1} : W))
    (fun c1 => ok ({c0 := toC c0,c1 := c1} : CW))
    (qm_add_maps_current x.c1 y.c1 hx.2 hy.2)
  intro c1
  rfl

#print axioms qm_add_maps_current
#print axioms actual_wide_add_maps_current
end AspisR1S9ActualPairWideAddCurrentV1
