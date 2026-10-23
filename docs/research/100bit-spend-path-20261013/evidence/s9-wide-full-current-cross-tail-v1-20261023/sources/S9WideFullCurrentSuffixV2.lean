import S9WideCurrentSharedMapAdapterV1
import S9WideFullCurrentSuffixV1
import S9WideSourceMulUCurrentV1
import S9WideSourceQMCanonicalV1
import S9WideSourceQMCurrentOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideFullCurrentSuffixV2

abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31

def qToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent
def mapPair (p : Q × Q) : C × C := (qToCurrent p.1, qToCurrent p.2)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutTailAfterCross (cross ac bd : Q) : Result (Q × Q) := do
  let q2 ← AspisR1S9WideSourceRecordMapV1.qcutMulUFormula bd
  let q3 ← AspisR1S9WideSourceQMAddV1.qcutQMAdd ac q2
  AspisR1S9WideFullCurrentSuffixV1.qcutTailAfterQ3 q3 cross ac bd

def currentTailAfterCross (cross ac bd : C) : Result (C × C) := do
  let q2 ← AspisR1CurrentWide.field.wide_exact.mul_u bd
  let q3 ← AspisR1CurrentWide.field.QM31.add ac q2
  AspisR1S9WideFullCurrentSuffixV1.currentTailAfterQ3 q3 cross ac bd

private theorem mulU_success_canonical (x z : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (h : AspisR1S9WideSourceRecordMapV1.qcutMulUFormula x = .ok z) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM z) := by
  obtain ⟨z', hz', _, hc, _⟩ :=
    AspisR1S9WideSourceQMCanonicalV1.qcut_mul_u_total_canonical x hx
  have hzz' : z = z' := Result.ok.inj (h.symm.trans hz')
  cases hzz'
  exact hc

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

/-- Extends the checked terminal subtraction suffix across the source
`mul_u` and following QM addition. Canonicality of both successful outputs
comes from the same source operations. -/
theorem qcut_tail_after_cross_maps_to_current (cross ac bd : Q)
    (hcross : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM cross))
    (hac : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM ac))
    (hbd : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM bd)) :
    mapResult mapPair (qcutTailAfterCross cross ac bd) =
      currentTailAfterCross (qToCurrent cross) (qToCurrent ac) (qToCurrent bd) := by
  unfold qcutTailAfterCross currentTailAfterCross
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_mul_u_maps_to_current bd hbd)
  intro q2 q2' hq2 hq2'
  have hq2can := mulU_success_canonical bd q2 hbd hq2
  cases hq2'
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_qm_add_maps_to_current ac q2 hac hq2can)
  intro q3 q3' hq3 hq3'
  have hq3can := add_success_canonical ac q2 q3 hac hq2can hq3
  cases hq3'
  exact AspisR1S9WideFullCurrentSuffixV1.qcut_tail_after_q3_maps_to_current
    q3 cross ac bd hcross hac hbd

#print axioms qcut_tail_after_cross_maps_to_current

end AspisR1S9WideFullCurrentSuffixV2
