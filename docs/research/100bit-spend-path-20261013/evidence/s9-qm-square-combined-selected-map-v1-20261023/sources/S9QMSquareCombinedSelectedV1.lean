import S9ActualQMSquareGraphV1
import S9QMSquareCombinedSelectedOpsV1
import S9QMSquareSuccessBindMapV1
import S9QMSquareSuccessCanonicalV1
import S9QMSquareSourceResultHeadV1
import ExtractedMaskQM31SquareExact

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareCombinedSelectedV1

abbrev SCM := AspisR1S9SquareMulQMCutV1.field.CM31
abbrev SQM := AspisR1S9SquareMulQMCutV1.field.QM31
abbrev TCM := AspisR1SelectedMaskProbe.field.CM31
abbrev TQM := AspisR1SelectedMaskProbe.field.QM31

abbrev toProbeCM := AspisR1S9QMSquareCombinedProbeOpsV1.toProbe
abbrev toSelectedCM := AspisR1S9QMSquareCombinedSelectedOpsV1.toSelected

def toSelectedQM (x : SQM) : TQM :=
  ⟨toSelectedCM x.c0, toSelectedCM x.c1⟩

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) :=
  AspisR1S9QMSquareSuccessBindMapV1.mapResult f r

def pairResult (a b : SCM) : Result SQM := .ok ⟨a, b⟩
def selectedPairResult (a b : TCM) : Result TQM := .ok ⟨a, b⟩

abbrev Canonical (x : SCM) :=
  AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbeCM x)

private theorem canonical_bounds (x : SCM) (hx : Canonical x) :
    x.a.val < 2147483647 ∧ x.b.val < 2147483647 := by
  constructor
  · simpa only [AspisR1S9QMSquareCombinedProbeOpsV1.toProbe,
      AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
      AspisR1.ExtractedCurrentTowerAdd.P,
      AspisR1.ExtractedCurrentM31AddSub.P] using hx.1
  · simpa only [AspisR1S9QMSquareCombinedProbeOpsV1.toProbe,
      AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
      AspisR1.ExtractedCurrentTowerAdd.P,
      AspisR1.ExtractedCurrentM31AddSub.P] using hx.2

/-- The final double and result construction, isolated to keep bind reduction
local and to preserve the actual selected operation calls. -/
theorem double_tail (out0 cross : SCM)
    (hcan : Canonical cross) :
    mapResult toSelectedQM
      (do
        let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
        pairResult out0 out1) =
      (do
        let out1 ← AspisR1SelectedMaskProbe.field.CM31.double (toSelectedCM cross)
        selectedPairResult (toSelectedCM out0) out1) := by
  have hdouble :=
    AspisR1S9QMSquareCombinedSelectedOpsV1.combined_cm_double_maps_to_selected
      cross hcan
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    (f := toSelectedQM) (g := toSelectedCM)
    (r := AspisR1S9SquareMulQMCutV1.field.CM31.double cross)
    (r' := AspisR1SelectedMaskProbe.field.CM31.double (toSelectedCM cross))
    (k := fun out1 => pairResult out0 out1)
    (k' := fun out1' => selectedPairResult (toSelectedCM out0) out1') hdouble ?_
  intro out1 out1' hout1 hout1map
  subst out1'
  rfl

/-- The cross product followed by the final double. -/
theorem cross_tail (x0 x1 out0 : SCM)
    (hcan0 : Canonical x0) (hcan1 : Canonical x1) :
    mapResult toSelectedQM
      (do
        let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x0 x1
        let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
        pairResult out0 out1) =
      (do
        let cross ← AspisR1SelectedMaskProbe.field.CM31.mul
          (toSelectedCM x0) (toSelectedCM x1)
        let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross
        selectedPairResult (toSelectedCM out0) out1) := by
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    (f := toSelectedQM) (g := toSelectedCM)
    (r := AspisR1S9SquareMulQMCutV1.field.CM31.mul x0 x1)
    (r' := AspisR1SelectedMaskProbe.field.CM31.mul
      (toSelectedCM x0) (toSelectedCM x1))
    (k := fun cross => do
      let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
      pairResult out0 out1)
    (k' := fun cross' => do
      let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross'
      selectedPairResult (toSelectedCM out0) out1)
    (AspisR1S9QMSquareCombinedSelectedOpsV1.combined_cm_mul_maps_to_selected
      x0 x1 hcan0 hcan1) ?_
  intro cross cross' hcall hmap
  subst cross'
  have hcan := AspisR1S9QMSquareSuccessCanonicalV1.cm_mul_success_canonical
    x0 x1 cross hcan0 hcan1 hcall
  exact double_tail out0 cross hcan

/-- The sum of the real component and rotated imaginary square, followed by
cross-product and double. -/
theorem add_tail (x0 x1 a0 rot : SCM)
    (hcan0 : Canonical a0) (hcanRot : Canonical rot)
    (hcanX0 : Canonical x0) (hcanX1 : Canonical x1) :
    mapResult toSelectedQM
      (do
        let out0 ← AspisR1S9SquareMulQMCutV1.field.CM31.add a0 rot
        let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x0 x1
        let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
        pairResult out0 out1) =
      (do
        let out0 ← AspisR1SelectedMaskProbe.field.CM31.add
          (toSelectedCM a0) (toSelectedCM rot)
        let cross ← AspisR1SelectedMaskProbe.field.CM31.mul
          (toSelectedCM x0) (toSelectedCM x1)
        let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross
        selectedPairResult out0 out1) := by
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    (f := toSelectedQM) (g := toSelectedCM)
    (r := AspisR1S9SquareMulQMCutV1.field.CM31.add a0 rot)
    (r' := AspisR1SelectedMaskProbe.field.CM31.add
      (toSelectedCM a0) (toSelectedCM rot))
    (k := fun out0 => do
      let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x0 x1
      let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
      pairResult out0 out1)
    (k' := fun out0' => do
      let cross ← AspisR1SelectedMaskProbe.field.CM31.mul
        (toSelectedCM x0) (toSelectedCM x1)
      let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross
      selectedPairResult out0' out1)
    (AspisR1S9QMSquareCombinedSelectedOpsV1.combined_cm_add_maps_to_selected
      a0 rot hcan0 hcanRot) ?_
  intro out0 out0' hcall hmap
  subst out0'
  exact cross_tail x0 x1 out0 hcanX0 hcanX1

/-- The by-r step followed by the remaining addition and product tail. -/
theorem by_r_tail (x0 x1 a0 a1 : SCM)
    (hcan0 : Canonical a0) (hcan1 : Canonical a1)
    (hcanX0 : Canonical x0) (hcanX1 : Canonical x1) :
    mapResult toSelectedQM
      (do
        let rot ← AspisR1S9SquareMulQMCutV1.field.mul_by_r a1
        let out0 ← AspisR1S9SquareMulQMCutV1.field.CM31.add a0 rot
        let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x0 x1
        let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
        pairResult out0 out1) =
      (do
        let rot ← AspisR1SelectedMaskProbe.field.mul_by_r (toSelectedCM a1)
        let out0 ← AspisR1SelectedMaskProbe.field.CM31.add
          (toSelectedCM a0) rot
        let cross ← AspisR1SelectedMaskProbe.field.CM31.mul
          (toSelectedCM x0) (toSelectedCM x1)
        let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross
        selectedPairResult out0 out1) := by
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    (f := toSelectedQM) (g := toSelectedCM)
    (r := AspisR1S9SquareMulQMCutV1.field.mul_by_r a1)
    (r' := AspisR1SelectedMaskProbe.field.mul_by_r (toSelectedCM a1))
    (k := fun rot => do
      let out0 ← AspisR1S9SquareMulQMCutV1.field.CM31.add a0 rot
      let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x0 x1
      let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
      pairResult out0 out1)
    (k' := fun rot' => do
      let out0 ← AspisR1SelectedMaskProbe.field.CM31.add
        (toSelectedCM a0) rot'
      let cross ← AspisR1SelectedMaskProbe.field.CM31.mul
        (toSelectedCM x0) (toSelectedCM x1)
      let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross
      selectedPairResult out0 out1)
    (AspisR1S9QMSquareCombinedSelectedOpsV1.combined_by_r_maps_to_selected
      a1 hcan1) ?_
  intro rot rot' hcall hmap
  subst rot'
  have hcanRot := AspisR1S9QMSquareSuccessCanonicalV1.by_r_success_canonical
    a1 rot hcan1 hcall
  exact add_tail x0 x1 a0 rot hcan0 hcanRot hcanX0 hcanX1

/-- The second component square, then the by-r and addition suffix. -/
theorem square1_tail (x0 x1 a0 : SCM)
    (hcan0 : Canonical a0) (hcanX0 : Canonical x0) (hcanX1 : Canonical x1) :
    mapResult toSelectedQM
      (do
        let a1 ← AspisR1S9SquareMulQMCutV1.field.CM31.square x1
        let rot ← AspisR1S9SquareMulQMCutV1.field.mul_by_r a1
        let out0 ← AspisR1S9SquareMulQMCutV1.field.CM31.add a0 rot
        let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x0 x1
        let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
        pairResult out0 out1) =
      (do
        let a1 ← AspisR1SelectedMaskProbe.field.CM31.square (toSelectedCM x1)
        let rot ← AspisR1SelectedMaskProbe.field.mul_by_r a1
        let out0 ← AspisR1SelectedMaskProbe.field.CM31.add
          (toSelectedCM a0) rot
        let cross ← AspisR1SelectedMaskProbe.field.CM31.mul
          (toSelectedCM x0) (toSelectedCM x1)
        let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross
        selectedPairResult out0 out1) := by
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    (f := toSelectedQM) (g := toSelectedCM)
    (r := AspisR1S9SquareMulQMCutV1.field.CM31.square x1)
    (r' := AspisR1SelectedMaskProbe.field.CM31.square (toSelectedCM x1))
    (k := fun a1 => do
      let rot ← AspisR1S9SquareMulQMCutV1.field.mul_by_r a1
      let out0 ← AspisR1S9SquareMulQMCutV1.field.CM31.add a0 rot
      let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x0 x1
      let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
      pairResult out0 out1)
    (k' := fun a1' => do
      let rot ← AspisR1SelectedMaskProbe.field.mul_by_r a1'
      let out0 ← AspisR1SelectedMaskProbe.field.CM31.add (toSelectedCM a0) rot
      let cross ← AspisR1SelectedMaskProbe.field.CM31.mul
        (toSelectedCM x0) (toSelectedCM x1)
      let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross
      selectedPairResult out0 out1)
    (AspisR1S9QMSquareSourceResultHeadV1.actual_square_result_maps_to_selected x1
      (canonical_bounds x1 hcanX1).1 (canonical_bounds x1 hcanX1).2) ?_
  intro a1 a1' hcall hmap
  subst a1'
  have hcan1 := AspisR1S9QMSquareSuccessCanonicalV1.cm_square_success_canonical
    x1 a1 hcanX1 hcall
  exact by_r_tail x0 x1 a0 a1 hcan0 hcan1 hcanX0 hcanX1

/-- Full source-level map for the extracted Combined-cut square. -/
theorem qm_square_maps_to_selected (x : SQM)
    (hx : Canonical x.c0 ∧ Canonical x.c1) :
    mapResult toSelectedQM
      (AspisR1S9SquareMulQMCutV1.field.QM31.square x) =
      AspisR1SelectedMaskProbe.field.QM31.square (toSelectedQM x) := by
  rw [AspisR1S9ActualQMSquareGraphV1.actual_qm_square_graph]
  unfold AspisR1SelectedMaskProbe.field.QM31.square
  have h0 := AspisR1S9QMSquareSourceResultHeadV1.actual_square_result_maps_to_selected
    x.c0 (canonical_bounds x.c0 hx.1).1 (canonical_bounds x.c0 hx.1).2
  have h1 := AspisR1S9QMSquareSourceResultHeadV1.actual_square_result_maps_to_selected
    x.c1 (canonical_bounds x.c1 hx.2).1 (canonical_bounds x.c1 hx.2).2
  apply AspisR1S9QMSquareSuccessBindMapV1.mapResult_bind_congr_of_success
    (f := toSelectedQM) (g := toSelectedCM)
    (r := AspisR1S9SquareMulQMCutV1.field.CM31.square x.c0)
    (r' := AspisR1SelectedMaskProbe.field.CM31.square (toSelectedCM x.c0))
    (k := fun a0 => do
      let a1 ← AspisR1S9SquareMulQMCutV1.field.CM31.square x.c1
      let rot ← AspisR1S9SquareMulQMCutV1.field.mul_by_r a1
      let out0 ← AspisR1S9SquareMulQMCutV1.field.CM31.add a0 rot
      let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x.c0 x.c1
      let out1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
      pairResult out0 out1)
    (k' := fun a0' => do
      let a1 ← AspisR1SelectedMaskProbe.field.CM31.square (toSelectedCM x.c1)
      let rot ← AspisR1SelectedMaskProbe.field.mul_by_r a1
      let out0 ← AspisR1SelectedMaskProbe.field.CM31.add a0' rot
      let cross ← AspisR1SelectedMaskProbe.field.CM31.mul
        (toSelectedCM x.c0) (toSelectedCM x.c1)
      let out1 ← AspisR1SelectedMaskProbe.field.CM31.double cross
      selectedPairResult out0 out1)
    h0 ?_
  intro a0 a0' hcall0 hmap0
  subst a0'
  have hcan0 := AspisR1S9QMSquareSuccessCanonicalV1.cm_square_success_canonical
    x.c0 a0 hx.1 hcall0
  exact square1_tail x.c0 x.c1 a0 hcan0 hx.1 hx.2

#print axioms double_tail
#print axioms cross_tail
#print axioms add_tail
#print axioms by_r_tail
#print axioms square1_tail
#print axioms qm_square_maps_to_selected

end AspisR1S9QMSquareCombinedSelectedV1
