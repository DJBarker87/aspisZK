import S9ActualPairMulM31CurrentV1
import S3S9ConcreteFieldOpsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualPairMulM31HelperTransportV1
open AspisR1S9ProductionPairCutV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev HW := AspisR1S9HelperP6.field.WideExact
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r
abbrev toCurrent := AspisR1S9ActualPairWideCanonicalV1.toCurrent
def toHelperW (x : W) : HW := AspisR1S9CurrentFieldOpsV1.fromE (toCurrent x)

/-- Full Result source transport for the concrete helper scalar operation.
The existing scalar arithmetic theorem covers every U32 scalar and operand,
so this bridge needs no independent canonicality or successful-call premise. -/
theorem actual_pair_wide_mul_m31_to_installed_helper (x : W) (s : U32) :
    mapResult toHelperW (aspis_core.field.wide_exact.WideExact.mul_m31 x s) =
      @AspisR1S9HelperP6.FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (toHelperW x) s := by
  have hsource := AspisR1S9ActualPairMulM31CurrentV1.actual_wide_mul_m31_maps_current x s
  have hhelper :
      @AspisR1S9HelperP6.FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (toHelperW x) s = mapResult AspisR1S9CurrentFieldOpsV1.fromE
          (AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toCurrent x) s) := by
    change (do
      let z ← AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
        (AspisR1S9CurrentFieldOpsV1.toE (AspisR1S9CurrentFieldOpsV1.fromE (toCurrent x))) s
      ok (AspisR1S9CurrentFieldOpsV1.fromE z)) = _
    rw [AspisR1S9CurrentFieldOpsV1.to_from]
    cases AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toCurrent x) s <;> rfl
  calc
    _ = mapResult AspisR1S9CurrentFieldOpsV1.fromE
      (mapResult toCurrent (aspis_core.field.wide_exact.WideExact.mul_m31 x s)) := by
        cases aspis_core.field.wide_exact.WideExact.mul_m31 x s <;> rfl
    _ = mapResult AspisR1S9CurrentFieldOpsV1.fromE
      (AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toCurrent x) s) :=
        congrArg (mapResult AspisR1S9CurrentFieldOpsV1.fromE) hsource
    _ = _ := hhelper.symm

#print axioms actual_pair_wide_mul_m31_to_installed_helper
end AspisR1S9ActualPairMulM31HelperTransportV1
