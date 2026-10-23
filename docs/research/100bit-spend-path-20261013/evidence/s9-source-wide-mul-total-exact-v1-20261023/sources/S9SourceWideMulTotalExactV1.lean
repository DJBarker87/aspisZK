import S9WideFullCurrentSourceV1
import S9ResultSuccessReflectionV1
import CurrentWideMulExactProduct
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SourceWideMulTotalExactV1
abbrev W := AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact
abbrev toCurrentWide := AspisR1S9WideFullCurrentSourceV1.toCurrentWide
abbrev toQQM := AspisR1S9WideSourceFullMapV1.toQQM
abbrev toProbeQM := AspisR1S9ActualQM31WrappingMapV1.toProbeQM

def Canonical (x : W) : Prop :=
  AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM (toQQM x.c0)) ∧
  AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbeQM (toQQM x.c1))

private theorem mapped_canonical (x : W) (hx : Canonical x) :
    AspisR1CurrentWide.Proof.CanonicalWide (toCurrentWide x) := by
  constructor
  · change AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1CurrentWide.Proof.toQM
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent (toQQM x.c0)))
    rw [AspisR1S9ActualQMCurrentHelperMapV1.probe_actualToCurrent]
    exact hx.1
  · change AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1CurrentWide.Proof.toQM
        (AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent (toQQM x.c1)))
    rw [AspisR1S9ActualQMCurrentHelperMapV1.probe_actualToCurrent]
    exact hx.2

/-- Exact same-run source multiplication, without an independent source-success premise. -/
theorem source_wide_mul_total_exact (x y : W)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide (toCurrentWide z) ∧
      AspisR1CurrentWide.Proof.decodeWide (toCurrentWide z) =
        AspisR1CurrentWide.Proof.decodeWide (toCurrentWide x) *
        AspisR1CurrentWide.Proof.decodeWide (toCurrentWide y) := by
  have hm := AspisR1S9WideFullCurrentSourceV1.source_wide_mul_maps_to_current
    x y hx.1 hx.2 hy.1 hy.2
  have ht := AspisR1CurrentWide.Proof.wide_mul_total_exact
    (toCurrentWide x) (toCurrentWide y) (mapped_canonical x hx) (mapped_canonical y hy)
  exact AspisR1S9ResultSuccessReflectionV1.source_success_of_target
    toCurrentWide (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y)
    (AspisR1CurrentWide.field.wide_exact.WideExact.mul (toCurrentWide x) (toCurrentWide y))
    (fun z => AspisR1CurrentWide.Proof.CanonicalWide z ∧
      AspisR1CurrentWide.Proof.decodeWide z =
        AspisR1CurrentWide.Proof.decodeWide (toCurrentWide x) *
        AspisR1CurrentWide.Proof.decodeWide (toCurrentWide y)) hm ht
#print axioms source_wide_mul_total_exact
end AspisR1S9SourceWideMulTotalExactV1
