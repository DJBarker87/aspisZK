import S9QMSquareCombinedProbeOpsV1
import S9CheckedProbeSelectedCMV1
import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareCombinedSelectedOpsV1

abbrev SCM := AspisR1S9SquareMulQMCutV1.field.CM31
abbrev PCM := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev TCM := AspisR1SelectedMaskProbe.field.CM31

abbrev toProbe := AspisR1S9QMSquareCombinedProbeOpsV1.toProbe
abbrev toSelectedProbe := AspisR1S9CheckedProbeSelectedCMV1.toSelectedCM

def toSelected (x : SCM) : TCM := toSelectedProbe (toProbe x)

abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f

private theorem mapResult_comp {A B C : Type} (f : B → C) (g : A → B)
    (r : Result A) :
    mapResult f (mapResult g r) = mapResult (fun x => f (g x)) r := by
  cases r <;> rfl

private theorem mapResult_ok_inv {A B : Type} (f : A → B) (r : Result A) (y : B)
    (h : mapResult f r = .ok y) :
    ∃ x, r = .ok x ∧ f x = y := by
  cases r with
  | ok x => exact ⟨x, rfl, Result.ok.inj h⟩
  | fail e => cases h
  | div => cases h

theorem combined_cm_add_maps_to_selected (x y : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe y)) :
    mapResult toSelected (AspisR1S9SquareMulQMCutV1.field.CM31.add x y) =
      AspisR1SelectedMaskProbe.field.CM31.add (toSelected x) (toSelected y) := by
  have hsource := AspisR1S9QMSquareCombinedProbeOpsV1.combined_cm_add_maps_to_probe x y hx hy
  have htarget := AspisR1S9CheckedProbeSelectedCMV1.cm_add_maps (toProbe x) (toProbe y)
  calc
    mapResult toSelected (AspisR1S9SquareMulQMCutV1.field.CM31.add x y) =
        mapResult toSelectedProbe
          (mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.CM31.add x y)) := by
            change mapResult (fun z => toSelectedProbe (toProbe z)) _ = _
            exact (mapResult_comp toSelectedProbe toProbe _).symm
    _ = mapResult toSelectedProbe
          (AspisR1Qm31ArithmeticProbe.field.CM31.add (toProbe x) (toProbe y)) :=
        congrArg (mapResult toSelectedProbe) hsource
    _ = AspisR1SelectedMaskProbe.field.CM31.add (toSelected x) (toSelected y) := by
        simpa only [toSelected] using htarget

theorem combined_cm_mul_maps_to_selected (x y : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe y)) :
    mapResult toSelected (AspisR1S9SquareMulQMCutV1.field.CM31.mul x y) =
      AspisR1SelectedMaskProbe.field.CM31.mul (toSelected x) (toSelected y) := by
  have hsource := AspisR1S9QMSquareCombinedProbeOpsV1.combined_cm_mul_maps_to_probe x y hx hy
  have htarget := AspisR1S9CheckedProbeSelectedCMV1.cm_mul_maps (toProbe x) (toProbe y)
  calc
    mapResult toSelected (AspisR1S9SquareMulQMCutV1.field.CM31.mul x y) =
        mapResult toSelectedProbe
          (mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.CM31.mul x y)) := by
            change mapResult (fun z => toSelectedProbe (toProbe z)) _ = _
            exact (mapResult_comp toSelectedProbe toProbe _).symm
    _ = mapResult toSelectedProbe
          (AspisR1Qm31ArithmeticProbe.field.CM31.mul (toProbe x) (toProbe y)) :=
        congrArg (mapResult toSelectedProbe) hsource
    _ = AspisR1SelectedMaskProbe.field.CM31.mul (toSelected x) (toSelected y) := by
        simpa only [toSelected] using htarget

theorem combined_by_r_maps_to_selected (x : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x)) :
    mapResult toSelected (AspisR1S9SquareMulQMCutV1.field.mul_by_r x) =
      AspisR1SelectedMaskProbe.field.mul_by_r (toSelected x) := by
  have hsource := AspisR1S9QMSquareCombinedProbeOpsV1.combined_by_r_maps_to_probe x hx
  have htarget := AspisR1S9CheckedProbeSelectedCMV1.by_r_maps (toProbe x)
  calc
    mapResult toSelected (AspisR1S9SquareMulQMCutV1.field.mul_by_r x) =
        mapResult toSelectedProbe
          (mapResult toProbe (AspisR1S9SquareMulQMCutV1.field.mul_by_r x)) := by
            change mapResult (fun z => toSelectedProbe (toProbe z)) _ = _
            exact (mapResult_comp toSelectedProbe toProbe _).symm
    _ = mapResult toSelectedProbe
          (AspisR1Qm31ArithmeticProbe.field.mul_by_r (toProbe x)) :=
        congrArg (mapResult toSelectedProbe) hsource
    _ = AspisR1SelectedMaskProbe.field.mul_by_r (toSelected x) := by
        simpa only [toSelected] using htarget

theorem combined_cm_double_maps_to_selected (x : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toProbe x)) :
    mapResult toSelected (AspisR1S9SquareMulQMCutV1.field.CM31.double x) =
      AspisR1SelectedMaskProbe.field.CM31.double (toSelected x) := by
  unfold AspisR1S9SquareMulQMCutV1.field.CM31.double
    AspisR1SelectedMaskProbe.field.CM31.double
  exact combined_cm_add_maps_to_selected x x hx hx

#print axioms combined_cm_add_maps_to_selected
#print axioms combined_cm_mul_maps_to_selected
#print axioms combined_by_r_maps_to_selected
#print axioms combined_cm_double_maps_to_selected

end AspisR1S9QMSquareCombinedSelectedOpsV1
