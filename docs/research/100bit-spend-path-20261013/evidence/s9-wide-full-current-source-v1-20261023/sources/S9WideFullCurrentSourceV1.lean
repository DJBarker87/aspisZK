import S9WideFullCurrentComposeV1
import S9WideSourceFullMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideFullCurrentSourceV1

abbrev SrcWide := AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact
abbrev DstWide := AspisR1CurrentWide.field.wide_exact.WideExact
abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31

def qToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent
def pairToWide (x : C × C) : DstWide := ⟨x.1, x.2⟩
def toCurrentWide (x : SrcWide) : DstWide :=
  pairToWide ((qToCurrent (AspisR1S9WideSourceFullMapV1.toQQM x.c0)),
    (qToCurrent (AspisR1S9WideSourceFullMapV1.toQQM x.c1)))

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

private theorem mapResult_comp {A B D : Type} (f : A → B) (g : B → D)
    (r : Result A) :
    mapResult g (mapResult f r) = mapResult (fun x => g (f x)) r := by
  cases r <;> rfl

private theorem mapResult_bind {A B D : Type} (f : B → D)
    (r : Result A) (k : A → Result B) :
    mapResult f (r >>= k) = r >>= (fun a => mapResult f (k a)) := by
  cases r <;> rfl

private theorem mapResult_ok {A B : Type} (f : A → B) (x : A) :
    mapResult f (Result.ok x) = Result.ok (f x) := rfl

private theorem mapResult_nested {A B C D : Type} (f : A → B)
    (g : B → C) (h : C → D) (r : Result A) :
    mapResult (h ∘ g ∘ f) r =
      mapResult h (mapResult g (mapResult f r)) := by
  cases r <;> rfl

private theorem current_formula_eq_operation (x y : C × C) :
    mapResult pairToWide
      (AspisR1S9WideFullCurrentComposeV1.currentFormula x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul
        (pairToWide x) (pairToWide y) := by
  unfold AspisR1S9WideFullCurrentComposeV1.currentFormula
    AspisR1S9WideFullCurrentSuffixV5.currentTailAfterInitialProducts
    AspisR1S9WideFullCurrentSuffixV4.currentTailAfterQ
    AspisR1S9WideFullCurrentSuffixV3.currentTailAfterQ1
    AspisR1S9WideFullCurrentSuffixV2.currentTailAfterCross
    AspisR1S9WideFullCurrentSuffixV1.currentTailAfterQ3
    AspisR1CurrentWide.field.wide_exact.WideExact.mul
  simp only [mapResult_bind, mapResult_ok, pairToWide]

/-- The exact transparent source WideExact.mul result, mapped through the
selected qcut and CurrentWide carriers, agrees with the checked CurrentWide
WideExact.mul result. Canonical component premises guard the wrapping-to-
checked arithmetic boundary. -/
theorem source_wide_mul_maps_to_current (x y : SrcWide)
    (hx0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM x.c0)))
    (hx1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM x.c1)))
    (hy0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM y.c0)))
    (hy1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM y.c1))) :
    mapResult toCurrentWide
      (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul
        (toCurrentWide x) (toCurrentWide y) := by
  have hsource := AspisR1S9WideSourceFullMapV1.wide_mul_maps_to_qcut_formula x y
  have hsource' := congrArg
    (mapResult AspisR1S9WideFullCurrentComposeV1.mapPair) hsource
  rw [← AspisR1S9WideFullCurrentComposeV1.qcutFormula_is_actual] at hsource'
  have hformula :=
    AspisR1S9WideFullCurrentComposeV1.qcut_formula_maps_to_current
      (AspisR1S9WideSourceFullMapV1.toQWide x)
      (AspisR1S9WideSourceFullMapV1.toQWide y) hx0 hx1 hy0 hy1
  change mapResult toCurrentWide
      (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) = _
  have hcarrier : toCurrentWide =
      (pairToWide ∘ AspisR1S9WideFullCurrentComposeV1.mapPair) ∘
        AspisR1S9WideSourceFullMapV1.toQWide := by
    funext z
    cases z
    rfl
  have hmap :
      mapResult toCurrentWide
          (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) =
        mapResult pairToWide
          (mapResult AspisR1S9WideFullCurrentComposeV1.mapPair
            (mapResult AspisR1S9WideSourceFullMapV1.toQWide
              (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y))) := by
    rw [hcarrier]
    exact mapResult_nested AspisR1S9WideSourceFullMapV1.toQWide
      AspisR1S9WideFullCurrentComposeV1.mapPair pairToWide
      (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y)
  calc
    mapResult toCurrentWide
        (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y) =
      mapResult pairToWide
        (mapResult AspisR1S9WideFullCurrentComposeV1.mapPair
          (mapResult AspisR1S9WideSourceFullMapV1.toQWide
            (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul x y))) := hmap
    _ = mapResult pairToWide
        (mapResult AspisR1S9WideFullCurrentComposeV1.mapPair
          (AspisR1S9WideFullCurrentComposeV1.qcutFormula
            (AspisR1S9WideSourceFullMapV1.toQWide x)
            (AspisR1S9WideSourceFullMapV1.toQWide y))) := by
          exact congrArg (mapResult pairToWide) hsource'
    _ = mapResult pairToWide
          (AspisR1S9WideFullCurrentComposeV1.currentFormula
            (AspisR1S9WideFullCurrentComposeV1.mapPair
              (AspisR1S9WideSourceFullMapV1.toQWide x))
            (AspisR1S9WideFullCurrentComposeV1.mapPair
              (AspisR1S9WideSourceFullMapV1.toQWide y))) :=
          congrArg (mapResult pairToWide) hformula
    _ = AspisR1CurrentWide.field.wide_exact.WideExact.mul
          (toCurrentWide x) (toCurrentWide y) := by
          rw [current_formula_eq_operation]
          rfl

#print axioms source_wide_mul_maps_to_current

end AspisR1S9WideFullCurrentSourceV1
