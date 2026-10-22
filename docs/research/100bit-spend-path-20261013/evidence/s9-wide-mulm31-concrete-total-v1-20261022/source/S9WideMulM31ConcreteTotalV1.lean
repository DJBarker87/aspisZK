import S9WideMulM31TotalExactV1
import S3S9ConcreteFieldOpsV1
import AspisR1S9HelperP6.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulM31ConcreteTotalV1

/-- The attempt16 source cut and the retained P6 helper use separate Lean
record declarations with identical field layout. -/
def sourceToP6W
    (x : AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact) :
    AspisR1S9HelperP6.field.WideExact :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

theorem toE_sourceToP6W
    (x : AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact) :
    AspisR1S9CurrentFieldOpsV1.toE (sourceToP6W x) =
      AspisR1S9WideMulM31FullResultMapV1.mapWide x := rfl

theorem fromE_mapWide
    (x : AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact) :
    AspisR1S9CurrentFieldOpsV1.fromE
      (AspisR1S9WideMulM31FullResultMapV1.mapWide x) = sourceToP6W x := rfl

/-- The installed concrete helper slot agrees on the full Result with the
actual attempt16 source call transported to the P6 carrier. -/
theorem concrete_wide_mul_m31_maps_source
    (x : AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact)
    (s : AspisR1S9WideMulM31CutV1.field.M31) :
    @AspisR1S9HelperP6.FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (sourceToP6W x) s =
      AspisR1S9WideMulM31FullResultMapV1.mapR sourceToP6W
        (AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact.mul_m31 x s) := by
  rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideMulM31_dispatch]
  unfold AspisR1S9ConcreteFieldOpsV1.actualWideMulM31
    AspisR1S9CurrentFieldOpsV1.actualWideMulM31
  rw [toE_sourceToP6W]
  have hmap := AspisR1S9WideMulM31UpperResultMapV1.wide_mul_m31_result_map x s
  cases hsrc :
      AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact.mul_m31 x s with
  | ok z =>
      rw [hsrc] at hmap
      have hcur :
          AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
            (AspisR1S9WideMulM31FullResultMapV1.mapWide x) s =
            .ok (AspisR1S9WideMulM31FullResultMapV1.mapWide z) := hmap.symm
      simp [hcur, fromE_mapWide, AspisR1S9WideMulM31FullResultMapV1.mapR, hsrc]
  | fail e =>
      rw [hsrc] at hmap
      have hcur :
          AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
            (AspisR1S9WideMulM31FullResultMapV1.mapWide x) s = .fail e := hmap.symm
      simp [hcur, AspisR1S9WideMulM31FullResultMapV1.mapR, hsrc]
  | div =>
      rw [hsrc] at hmap
      have hcur :
          AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
            (AspisR1S9WideMulM31FullResultMapV1.mapWide x) s = .div := hmap.symm
      simp [hcur, AspisR1S9WideMulM31FullResultMapV1.mapR, hsrc]

/-- For canonical mapped inputs, the concrete installed helper call succeeds;
its returned value is the very source-cut result transported through the
explicit P6 carrier map, with canonicality and decode meaning. -/
theorem concrete_wide_mul_m31_total_exact
    (x : AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact)
    (s : AspisR1S9WideMulM31CutV1.field.M31)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9WideMulM31FullResultMapV1.mapWide x)) :
    ∃ z, @AspisR1S9HelperP6.FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (sourceToP6W x) s = .ok z ∧
      AspisR1S9CurrentFieldOpsV1.Canonical z ∧
      AspisR1S9CurrentFieldOpsV1.decode z =
        AspisR1CurrentWide.Proof.decodeWide
          (AspisR1S9WideMulM31FullResultMapV1.mapWide x) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding s := by
  obtain ⟨y, hy, hcan, hdecode⟩ :=
    AspisR1S9WideMulM31TotalExactV1.actual_wide_mul_m31_total_exact x s hx
  refine ⟨sourceToP6W y, ?_, ?_, ?_⟩
  · rw [concrete_wide_mul_m31_maps_source, hy]
    rfl
  · change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE (sourceToP6W y))
    rw [toE_sourceToP6W]
    exact hcan
  · change AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9CurrentFieldOpsV1.toE (sourceToP6W y)) = _
    rw [toE_sourceToP6W]
    exact hdecode

#print axioms toE_sourceToP6W
#print axioms fromE_mapWide
#print axioms concrete_wide_mul_m31_maps_source
#print axioms concrete_wide_mul_m31_total_exact

end AspisR1S9WideMulM31ConcreteTotalV1
