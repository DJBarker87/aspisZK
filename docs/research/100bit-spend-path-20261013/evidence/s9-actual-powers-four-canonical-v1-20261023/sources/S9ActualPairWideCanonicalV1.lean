import S9ActualPairWideResultMapV1
import S9WideFullCurrentSourceV1
import CurrentWideMulExactProduct

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualPairWideCanonicalV1
abbrev W := AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact
abbrev OldW := AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact
abbrev CW := AspisR1CurrentWide.field.wide_exact.WideExact
abbrev QQ := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def toOld (x : W) : OldW :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def toCurrent (x : W) : CW := AspisR1S9WideFullCurrentSourceV1.toCurrentWide (toOld x)
def Canonical (x : W) : Prop := AspisR1CurrentWide.Proof.CanonicalWide (toCurrent x)

private def pairToCurrent (x : QQ × QQ) : CW :=
  AspisR1S9WideFullCurrentSourceV1.pairToWide
    (AspisR1S9WideFullCurrentComposeV1.mapPair x)

private theorem actual_map_factor (r : Result W) :
    mapResult pairToCurrent
      (mapResult AspisR1S9ActualPairWideResultMapV1.toQWide r) =
      mapResult toCurrent r := by
  cases r <;> rfl

private theorem old_map_factor (r : Result OldW) :
    mapResult pairToCurrent
      (mapResult AspisR1S9WideSourceFullMapV1.toQWide r) =
      mapResult AspisR1S9WideFullCurrentSourceV1.toCurrentWide r := by
  cases r <;> rfl

/-- Full Result transport for the actual Pair Wide multiplication under the
canonical-input guard required by the already proved checked arithmetic. -/
theorem actual_wide_mul_maps_current (x y : W) (hx : Canonical x) (hy : Canonical y) :
    mapResult toCurrent
      (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul (toCurrent x) (toCurrent y) := by
  have hnew := AspisR1S9ActualPairWideResultMapV1.wide_mul_maps_to_qcut_formula x y
  have hold := AspisR1S9WideSourceFullMapV1.wide_mul_maps_to_qcut_formula (toOld x) (toOld y)
  have hq : mapResult AspisR1S9ActualPairWideResultMapV1.toQWide
      (AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul x y) =
      mapResult AspisR1S9WideSourceFullMapV1.toQWide
        (AspisR1S9ActualWideMulCutV1.field.wide_exact.WideExact.mul (toOld x) (toOld y)) :=
    hnew.trans hold.symm
  have hm := congrArg (mapResult pairToCurrent) hq
  rw [actual_map_factor, old_map_factor] at hm
  have hx0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM (toOld x).c0)) := hx.1
  have hx1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM (toOld x).c1)) := hx.2
  have hy0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM (toOld y).c0)) := hy.1
  have hy1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
        (AspisR1S9WideSourceFullMapV1.toQQM (toOld y).c1)) := hy.2
  exact hm.trans (AspisR1S9WideFullCurrentSourceV1.source_wide_mul_maps_to_current
    (toOld x) (toOld y) hx0 hx1 hy0 hy1)

/-- Canonicality is obtained from the successful multiplication made by the
same actual powers execution, rather than a supplied output contract. -/
theorem actual_wide_mul_success_canonical (x y z : W)
    (hx : Canonical x) (hy : Canonical y)
    (h : AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul x y = .ok z) :
    Canonical z := by
  have hm := actual_wide_mul_maps_current x y hx hy
  rw [h] at hm
  have hc : AspisR1CurrentWide.field.wide_exact.WideExact.mul
      (toCurrent x) (toCurrent y) = .ok (toCurrent z) := hm.symm
  exact (AspisR1CurrentWide.Proof.wide_mul_success_exact
    (toCurrent x) (toCurrent y) (toCurrent z) hx hy hc).1

#print axioms actual_wide_mul_maps_current
#print axioms actual_wide_mul_success_canonical
end AspisR1S9ActualPairWideCanonicalV1
