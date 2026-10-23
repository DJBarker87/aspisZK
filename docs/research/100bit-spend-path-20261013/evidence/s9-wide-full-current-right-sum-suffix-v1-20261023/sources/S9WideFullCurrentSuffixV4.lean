import S9WideCurrentSharedMapAdapterV1
import S9WideFullCurrentSuffixV3
import S9WideSourceQMCurrentOpsV1
import S9WideSourceQMCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideFullCurrentSuffixV4

abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31

def qToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent
def mapPair (p : Q × Q) : C × C := (qToCurrent p.1, qToCurrent p.2)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutTailAfterQ (q y0 y1 ac bd : Q) : Result (Q × Q) := do
  let q1 ← AspisR1S9WideSourceQMAddV1.qcutQMAdd y0 y1
  AspisR1S9WideFullCurrentSuffixV3.qcutTailAfterQ1 q q1 ac bd

def currentTailAfterQ (q y0 y1 ac bd : C) : Result (C × C) := do
  let q1 ← AspisR1CurrentWide.field.QM31.add y0 y1
  AspisR1S9WideFullCurrentSuffixV3.currentTailAfterQ1 q q1 ac bd

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

/-- Maps the source second sum and then the remaining multiplication suffix.
The sum result's canonicality is derived from the source add call. -/
theorem qcut_tail_after_q_maps_to_current (q y0 y1 ac bd : Q)
    (hq : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM q))
    (hy0 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y0))
    (hy1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y1))
    (hac : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM ac))
    (hbd : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM bd)) :
    mapResult mapPair (qcutTailAfterQ q y0 y1 ac bd) =
      currentTailAfterQ (qToCurrent q) (qToCurrent y0) (qToCurrent y1)
        (qToCurrent ac) (qToCurrent bd) := by
  unfold qcutTailAfterQ currentTailAfterQ
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_qm_add_maps_to_current y0 y1 hy0 hy1)
  intro q1 q1' hq1 hq1'
  have hq1can := add_success_canonical y0 y1 q1 hy0 hy1 hq1
  cases hq1'
  exact AspisR1S9WideFullCurrentSuffixV3.qcut_tail_after_q1_maps_to_current
    q q1 ac bd hq hq1can hac hbd

#print axioms qcut_tail_after_q_maps_to_current

end AspisR1S9WideFullCurrentSuffixV4
