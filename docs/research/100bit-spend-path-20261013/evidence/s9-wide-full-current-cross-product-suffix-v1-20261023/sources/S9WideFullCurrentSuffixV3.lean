import S9WideCurrentSharedMapAdapterV1
import S9WideFullCurrentSuffixV2
import S9WideSourceQMMulCurrentV1
import S9ActualQM31TotalCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideFullCurrentSuffixV3

abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31

def qToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent
def mapPair (p : Q × Q) : C × C := (qToCurrent p.1, qToCurrent p.2)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutTailAfterQ1 (q q1 ac bd : Q) : Result (Q × Q) := do
  let cross ← AspisR1S9ActualQMMulCutV1.field.QM31.mul q q1
  AspisR1S9WideFullCurrentSuffixV2.qcutTailAfterCross cross ac bd

def currentTailAfterQ1 (q q1 ac bd : C) : Result (C × C) := do
  let cross ← AspisR1CurrentWide.field.QM31.mul q q1
  AspisR1S9WideFullCurrentSuffixV2.currentTailAfterCross cross ac bd

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

/-- The cross-product call maps together with the actual mul_u/add/sub suffix.
The cross output's canonicality is derived from that successful call. -/
theorem qcut_tail_after_q1_maps_to_current (q q1 ac bd : Q)
    (hq : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM q))
    (hq1 : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM q1))
    (hac : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM ac))
    (hbd : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM bd)) :
    mapResult mapPair (qcutTailAfterQ1 q q1 ac bd) =
      currentTailAfterQ1 (qToCurrent q) (qToCurrent q1)
        (qToCurrent ac) (qToCurrent bd) := by
  unfold qcutTailAfterQ1 currentTailAfterQ1
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_qm_mul_maps_to_current q q1 hq hq1)
  intro cross cross' hcross hcross'
  have hcrosscan := mul_success_canonical q q1 cross hq hq1 hcross
  cases hcross'
  exact AspisR1S9WideFullCurrentSuffixV2.qcut_tail_after_cross_maps_to_current
    cross ac bd hcrosscan hac hbd

#print axioms qcut_tail_after_q1_maps_to_current

end AspisR1S9WideFullCurrentSuffixV3
