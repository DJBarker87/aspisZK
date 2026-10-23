import S9WideCurrentSharedMapAdapterV1
import S9WideFullCurrentSuffixV4
import S9WideSourceQMCurrentOpsV1
import S9WideSourceQMCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideFullCurrentSuffixV5

abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31

def qToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent
def mapPair (p : Q × Q) : C × C := (qToCurrent p.1, qToCurrent p.2)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutTailAfterInitialProducts (x0 x1 y0 y1 ac bd : Q) : Result (Q × Q) := do
  let q ← AspisR1S9WideSourceQMAddV1.qcutQMAdd x0 x1
  AspisR1S9WideFullCurrentSuffixV4.qcutTailAfterQ q y0 y1 ac bd

def currentTailAfterInitialProducts (x0 x1 y0 y1 ac bd : C) : Result (C × C) := do
  let q ← AspisR1CurrentWide.field.QM31.add x0 x1
  AspisR1S9WideFullCurrentSuffixV4.currentTailAfterQ q y0 y1 ac bd

private theorem add_success_canonical (x y z : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y))
    (h : AspisR1S9WideSourceQMAddV1.qcutQMAdd x y = .ok z) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM z) := by
  obtain ⟨z', hz', _, hc, _⟩ :=
    AspisR1S9WideSourceQMCanonicalV1.qcut_qm_add_total_canonical x y hx hy
  have hzz' : z = z' := Result.ok.inj (h.symm.trans hz')
  cases hzz'
  exact hc

/-- Maps the first QM addition and delegates the remaining generated formula
tail, retaining only canonical input contracts and deriving the add result's
canonicality from its actual successful call. -/
theorem qcut_tail_after_initial_products_maps_to_current
    (x0 x1 y0 y1 ac bd : Q)
    (hx0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x0))
    (hx1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x1))
    (hy0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y0))
    (hy1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y1))
    (hac : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM ac))
    (hbd : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM bd)) :
    mapResult mapPair (qcutTailAfterInitialProducts x0 x1 y0 y1 ac bd) =
      currentTailAfterInitialProducts (qToCurrent x0) (qToCurrent x1)
        (qToCurrent y0) (qToCurrent y1) (qToCurrent ac) (qToCurrent bd) := by
  unfold qcutTailAfterInitialProducts currentTailAfterInitialProducts
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_qm_add_maps_to_current x0 x1 hx0 hx1)
  intro q q' hq hq'
  have hqcan := add_success_canonical x0 x1 q hx0 hx1 hq
  cases hq'
  exact AspisR1S9WideFullCurrentSuffixV4.qcut_tail_after_q_maps_to_current
    q y0 y1 ac bd hqcan hy0 hy1 hac hbd

#print axioms qcut_tail_after_initial_products_maps_to_current

end AspisR1S9WideFullCurrentSuffixV5
