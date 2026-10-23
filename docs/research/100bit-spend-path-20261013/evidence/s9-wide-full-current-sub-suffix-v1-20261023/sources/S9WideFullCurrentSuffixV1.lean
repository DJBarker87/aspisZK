import S9WideCurrentSharedMapAdapterV1
import S9SourceResultTransportV1
import S9QMSquareSuccessBindMapV1
import CurrentWideQMBridge

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideFullCurrentSuffixV1

abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31

def qToCurrent := AspisR1S9WideCurrentSharedMapAdapterV1.qToCurrent
def mapPair (p : Q × Q) : C × C := (qToCurrent p.1, qToCurrent p.2)
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

def qcutTailAfterQ3 (q3 cross ac bd : Q) : Result (Q × Q) := do
  let q4 ← AspisR1S9WideSourceQMSubV1.qcutQMSub cross ac
  let q5 ← AspisR1S9WideSourceQMSubV1.qcutQMSub q4 bd
  ok (q3, q5)

def currentTailAfterQ3 (q3 cross ac bd : C) : Result (C × C) := do
  let q4 ← AspisR1CurrentWide.field.QM31.sub cross ac
  let q5 ← AspisR1CurrentWide.field.QM31.sub q4 bd
  ok (q3, q5)

private theorem sub_success_canonical (x y z : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y))
    (h : AspisR1S9WideSourceQMSubV1.qcutQMSub x y = .ok z) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM z) := by
  obtain ⟨z', hz', _, hc, _, _⟩ :=
    AspisR1S9WideSourceQMCanonicalV1.qcut_qm_sub_total_canonical x y hx hy
  have hzz' : z = z' := Result.ok.inj (h.symm.trans hz')
  cases hzz'
  exact hc

/-- Two final subtractions of the actual qcut formula map to the checked
CurrentWide subtractions. The canonicality of the first subtraction result is
derived from the same successful source call and the qcut total/canonical law. -/
theorem qcut_tail_after_q3_maps_to_current (q3 cross ac bd : Q)
    (hcross : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM cross))
    (hac : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM ac))
    (hbd : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM bd)) :
    mapResult mapPair (qcutTailAfterQ3 q3 cross ac bd) =
      currentTailAfterQ3 (qToCurrent q3) (qToCurrent cross)
        (qToCurrent ac) (qToCurrent bd) := by
  unfold qcutTailAfterQ3 currentTailAfterQ3
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_qm_sub_maps_to_current
      cross ac hcross hac)
  intro q4 q4' hq4 hq4'
  have hq4can := sub_success_canonical cross ac q4 hcross hac hq4
  cases hq4'
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    mapPair qToCurrent _ _ _ _
    (AspisR1S9WideCurrentSharedMapAdapterV1.qcut_qm_sub_maps_to_current
      q4 bd hq4can hbd)
  intro q5 q5' hq5 hq5'
  cases hq5'
  rfl

#print axioms qcut_tail_after_q3_maps_to_current

end AspisR1S9WideFullCurrentSuffixV1
