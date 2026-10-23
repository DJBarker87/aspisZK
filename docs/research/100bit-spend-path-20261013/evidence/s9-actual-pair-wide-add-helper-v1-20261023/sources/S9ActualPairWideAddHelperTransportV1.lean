import S9ActualPairWideAddCurrentV1
import S3S9ConcreteFieldOpsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairWideAddHelperTransportV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev HW := AspisR1S9HelperP6.field.WideExact
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r
abbrev Canonical := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev toCurrent := AspisR1S9ActualPairWideCanonicalV1.toCurrent
def toHelperW (x : W) : HW := AspisR1S9CurrentFieldOpsV1.fromE (toCurrent x)

/-- Reuses the actual source addition proof and installed CurrentWide
helper implementation. The full Result transport retains every failure case. -/
theorem actual_pair_wide_add_to_installed_helper (x y : W)
    (hx : Canonical x) (hy : Canonical y) :
    mapResult toHelperW (aspis_core.field.wide_exact.WideExact.add x y) =
      @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (toHelperW x) (toHelperW y) := by
  have hsource := AspisR1S9ActualPairWideAddCurrentV1.actual_wide_add_maps_current x y hx hy
  have hhelper :
      @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (toHelperW x) (toHelperW y) =
      mapResult AspisR1S9CurrentFieldOpsV1.fromE
        (AspisR1CurrentWide.field.wide_exact.WideExact.add (toCurrent x) (toCurrent y)) := by
    change (do
      let z ← AspisR1CurrentWide.field.wide_exact.WideExact.add
        (AspisR1S9CurrentFieldOpsV1.toE (AspisR1S9CurrentFieldOpsV1.fromE (toCurrent x)))
        (AspisR1S9CurrentFieldOpsV1.toE (AspisR1S9CurrentFieldOpsV1.fromE (toCurrent y)))
      ok (AspisR1S9CurrentFieldOpsV1.fromE z)) = _
    rw [AspisR1S9CurrentFieldOpsV1.to_from,AspisR1S9CurrentFieldOpsV1.to_from]
    cases AspisR1CurrentWide.field.wide_exact.WideExact.add (toCurrent x) (toCurrent y) <;> rfl
  calc
    mapResult toHelperW (aspis_core.field.wide_exact.WideExact.add x y) =
        mapResult AspisR1S9CurrentFieldOpsV1.fromE
          (mapResult toCurrent (aspis_core.field.wide_exact.WideExact.add x y)) := by
            cases aspis_core.field.wide_exact.WideExact.add x y <;> rfl
    _ = mapResult AspisR1S9CurrentFieldOpsV1.fromE
        (AspisR1CurrentWide.field.wide_exact.WideExact.add (toCurrent x) (toCurrent y)) :=
      congrArg (mapResult AspisR1S9CurrentFieldOpsV1.fromE) hsource
    _ = _ := hhelper.symm

#print axioms actual_pair_wide_add_to_installed_helper
end AspisR1S9ActualPairWideAddHelperTransportV1
