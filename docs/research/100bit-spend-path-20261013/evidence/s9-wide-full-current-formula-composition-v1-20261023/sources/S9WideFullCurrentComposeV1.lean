import S9WideCurrentSharedMapAdapterV1
import S9WideFullCurrentSuffixV5
import S9WideSourceFullMapV1
import S9ActualQM31TotalCanonicalV1
import S9QMSquareSuccessBindMapV1
import CurrentWideQMBridge

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideFullCurrentComposeV1

abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31

def qToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent
def mapPair (p : Q × Q) : C × C := (qToCurrent p.1, qToCurrent p.2)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutFormula (x y : Q × Q) : Result (Q × Q) := do
  let ac ← AspisR1S9ActualQMMulCutV1.field.QM31.mul x.1 y.1
  let bd ← AspisR1S9ActualQMMulCutV1.field.QM31.mul x.2 y.2
  AspisR1S9WideFullCurrentSuffixV5.qcutTailAfterInitialProducts
    x.1 x.2 y.1 y.2 ac bd

def currentFormula (x y : C × C) : Result (C × C) := do
  let ac ← AspisR1CurrentWide.field.QM31.mul x.1 y.1
  let bd ← AspisR1CurrentWide.field.QM31.mul x.2 y.2
  AspisR1S9WideFullCurrentSuffixV5.currentTailAfterInitialProducts
    x.1 x.2 y.1 y.2 ac bd

/-- This staging is definitionally the actual qcut formula: the first two
product calls are explicit here, and the already-checked suffix names the
remaining source statements in their original order. -/
theorem qcutFormula_is_actual (x y : Q × Q) :
    qcutFormula x y = AspisR1S9WideSourceFullMapV1.qcutWideMulFormula x y := by
  rfl

private theorem mul_success_canonical (x y z : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y))
    (h : AspisR1S9ActualQMMulCutV1.field.QM31.mul x y = .ok z) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM z) := by
  obtain ⟨z', hz', hc⟩ :=
    AspisR1S9ActualQM31TotalCanonicalV1.actual_qm_mul_total_canonical x y hx hy
  have hzz' : z = z' := Result.ok.inj (h.symm.trans hz')
  cases hzz'
  exact hc

/-- Same-result checked refinement of the first two qcut products followed by
SuffixV5, which covers the remaining seven source operations. The only inputs
are the four canonical operand contracts; successful intermediate
canonicality is derived from each exact operation result. -/
theorem qcut_formula_maps_to_current (x y : Q × Q)
    (hx0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x.1))
    (hx1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x.2))
    (hy0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y.1))
    (hy1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y.2)) :
    mapResult mapPair (qcutFormula x y) =
      currentFormula (mapPair x) (mapPair y) := by
  unfold qcutFormula currentFormula
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_qm_mul_maps_to_current
      x.1 y.1 hx0 hy0)
  intro ac ac' hac hac'
  have hacan := mul_success_canonical x.1 y.1 ac hx0 hy0 hac
  cases hac'
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_qm_mul_maps_to_current
      x.2 y.2 hx1 hy1)
  intro bd bd' hbd hbd'
  have hbdcan := mul_success_canonical x.2 y.2 bd hx1 hy1 hbd
  cases hbd'
  exact AspisR1S9WideFullCurrentSuffixV5.qcut_tail_after_initial_products_maps_to_current
    x.1 x.2 y.1 y.2 ac bd hx0 hx1 hy0 hy1 hacan hbdcan

#print axioms qcutFormula_is_actual
#print axioms qcut_formula_maps_to_current

end AspisR1S9WideFullCurrentComposeV1
