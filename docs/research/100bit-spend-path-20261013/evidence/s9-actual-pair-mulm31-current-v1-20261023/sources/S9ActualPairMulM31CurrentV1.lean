import S9ActualPairWideCanonicalV1
import S9WideMulM31UpperResultMapV1
import S9QMMulM31PrimitiveSourceBridgeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualPairMulM31CurrentV1
open AspisR1S9ProductionPairCutV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev CM := aspis_core.field.CM31
abbrev QM := aspis_core.field.QM31
abbrev SC := AspisR1S9WideMulM31CutV1.field.CM31
abbrev SQ := AspisR1S9WideMulM31CutV1.field.QM31
abbrev SW := AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact
abbrev mapR := @AspisR1S9WideMulM31FullResultMapV1.mapR
abbrev mapR_bind := @AspisR1S9WideMulM31FullResultMapV1.mapR_bind
abbrev bind_mapR := @AspisR1S9WideMulM31UpperResultMapV1.bind_mapR

def toSC (x : CM) : SC := ⟨x.a,x.b⟩
def toSQ (x : QM) : SQ := ⟨toSC x.c0,toSC x.c1⟩
def toSW (x : W) : SW := ⟨toSQ x.c0,toSQ x.c1⟩

theorem m31_mul_same (x y : U32) : aspis_core.field.M31.mul x y =
    AspisR1S9WideMulM31CutV1.field.M31.mul x y :=
  (AspisR1S9PairSourceQMMulMapV1.m31_mul_same x y).trans
    (AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_mul_eq_scalar x y)

theorem cm_mul_m31_maps (x : CM) (s : U32) :
    mapR toSC (aspis_core.field.CM31.mul_m31 x s) =
      AspisR1S9WideMulM31CutV1.field.CM31.mul_m31 (toSC x) s := by
  unfold aspis_core.field.CM31.mul_m31 AspisR1S9WideMulM31CutV1.field.CM31.mul_m31
  simp only [mapR_bind,toSC,m31_mul_same]
  rfl

theorem qm_mul_m31_maps (x : QM) (s : U32) :
    mapR toSQ (aspis_core.field.QM31.mul_m31 x s) =
      AspisR1S9WideMulM31CutV1.field.QM31.mul_m31 (toSQ x) s := by
  unfold aspis_core.field.QM31.mul_m31 AspisR1S9WideMulM31CutV1.field.QM31.mul_m31
  simp only [toSQ]
  rw [←cm_mul_m31_maps x.c0 s,←cm_mul_m31_maps x.c1 s]
  simp only [mapR_bind,bind_mapR,toSQ,toSC]
  rfl

theorem wide_mul_m31_maps (x : W) (s : U32) :
    mapR toSW (aspis_core.field.wide_exact.WideExact.mul_m31 x s) =
      AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact.mul_m31 (toSW x) s := by
  unfold aspis_core.field.wide_exact.WideExact.mul_m31
    AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact.mul_m31
    aspis_core.field.P AspisR1S9WideMulM31CutV1.field.P
  simp only [toSW]
  simp only [←qm_mul_m31_maps]
  simp only [mapR_bind,bind_mapR,toSW,toSQ,toSC]
  rfl

/-- Scalar multiplication source transport reuses the full existing scalar
cut theorem. The scalar is arbitrary U32: the actual method retains its %P.
No successful-call or canonical-output premise is assumed. -/
theorem actual_wide_mul_m31_maps_current (x : W) (s : U32) :
    mapR AspisR1S9ActualPairWideCanonicalV1.toCurrent
      (aspis_core.field.wide_exact.WideExact.mul_m31 x s) =
    AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent x) s := by
  have hm := congrArg (mapR AspisR1S9WideMulM31FullResultMapV1.mapWide)
    (wide_mul_m31_maps x s)
  have hc := AspisR1S9WideMulM31UpperResultMapV1.wide_mul_m31_result_map (toSW x) s
  have he : mapR AspisR1S9WideMulM31FullResultMapV1.mapWide
      (mapR toSW (aspis_core.field.wide_exact.WideExact.mul_m31 x s)) =
      mapR AspisR1S9ActualPairWideCanonicalV1.toCurrent
        (aspis_core.field.wide_exact.WideExact.mul_m31 x s) := by
    cases aspis_core.field.wide_exact.WideExact.mul_m31 x s <;> rfl
  exact he.symm.trans (hm.trans hc)

#print axioms m31_mul_same
#print axioms cm_mul_m31_maps
#print axioms qm_mul_m31_maps
#print axioms wide_mul_m31_maps
#print axioms actual_wide_mul_m31_maps_current
end AspisR1S9ActualPairMulM31CurrentV1
