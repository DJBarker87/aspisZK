import S3S9ConcreteFieldOpsV1
import S9QMSquareCombinedSelectedV1
import ExtractedMaskQM31SquareExact
import KpowersCurrentQMSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareHelperSourceBridgeV1

local instance currentFieldOpsForSemantics : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps

abbrev CQ := AspisR1S9HelperP6.field.QM31
abbrev SQ := AspisR1SelectedMaskProbe.field.QM31
abbrev XQ := AspisR1S9SquareMulQMCutV1.field.QM31
abbrev Sem := AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics

def toSelected (x : CQ) : SQ :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def fromSelected (x : SQ) : CQ :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def toCutCM (x : AspisR1S9HelperP6.field.CM31) :
    AspisR1S9SquareMulQMCutV1.field.CM31 := ⟨x.a, x.b⟩

def toCut (x : CQ) : XQ := ⟨toCutCM x.c0, toCutCM x.c1⟩

def fromCutCM (x : AspisR1S9SquareMulQMCutV1.field.CM31) :
    AspisR1S9HelperP6.field.CM31 := ⟨x.a, x.b⟩

def fromCut (x : XQ) : CQ := ⟨fromCutCM x.c0, fromCutCM x.c1⟩

def toSelectedCut (x : XQ) : SQ :=
  ⟨AspisR1S9QMSquareCombinedSelectedOpsV1.toSelected x.c0,
   AspisR1S9QMSquareCombinedSelectedOpsV1.toSelected x.c1⟩

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) :=
  AspisR1S9SourceResultTransportV1.mapResult f r

private theorem mapResult_comp {A B C : Type} (f : B → C) (g : A → B)
    (r : Result A) :
    mapResult f (mapResult g r) = mapResult (fun x => f (g x)) r := by
  cases r <;> rfl

private theorem current_canonical_iff_selected (x : CQ) :
    Sem.canonical x ↔
      AspisR1.ExtractedMaskQM31SquareExact.CanonicalQM (toSelected x) := by
  cases x with
  | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl

private theorem helper_probe_cm_canonical (x : AspisR1S9HelperP6.field.CM31)
    (h : AspisR1.ExtractedMaskTowerAdd.CanonicalCM
      (⟨x.a, x.b⟩ : AspisR1SelectedMaskProbe.field.CM31)) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe (toCutCM x)) := by
  change x.a.val < AspisR1.ExtractedMaskM31AddSub.P ∧
    x.b.val < AspisR1.ExtractedMaskM31AddSub.P at h
  change x.a.val < AspisR1.ExtractedCurrentM31AddSub.P ∧
    x.b.val < AspisR1.ExtractedCurrentM31AddSub.P
  simpa only [AspisR1.ExtractedMaskM31AddSub.P,
    AspisR1.ExtractedCurrentM31AddSub.P] using h

private theorem helper_probe_canonical (x : CQ) (hx : Sem.canonical x) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe (toCutCM x.c0)) ∧
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe (toCutCM x.c1)) := by
  have hs := (current_canonical_iff_selected x).mp hx
  change AspisR1.ExtractedMaskTowerAdd.CanonicalCM (⟨x.c0.a, x.c0.b⟩ :
      AspisR1SelectedMaskProbe.field.CM31) ∧
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM (⟨x.c1.a, x.c1.b⟩ :
      AspisR1SelectedMaskProbe.field.CM31) at hs
  exact ⟨helper_probe_cm_canonical x.c0 hs.1,
    helper_probe_cm_canonical x.c1 hs.2⟩

theorem actual_qm_square_maps_to_installed_helper (x : CQ)
    (hx : Sem.canonical x) :
    mapResult fromCut
      (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x)) =
      AspisR1S9ConcreteFieldOpsV1.actualQMSquare x := by
  have hprobe := helper_probe_canonical x hx
  have hselected :=
    AspisR1S9QMSquareCombinedSelectedV1.qm_square_maps_to_selected
      (toCut x) hprobe
  have hround : fromCut = fun z : XQ => fromSelected (toSelectedCut z) := by
    funext z
    cases z with
    | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl
  have hmapper :
      AspisR1S9QMSquareCombinedSelectedV1.toSelectedQM = toSelectedCut := by
    funext z
    cases z with
    | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl
  have hinput :
      AspisR1S9QMSquareCombinedSelectedV1.toSelectedQM (toCut x) = toSelected x := by
    cases x with
    | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl
  have hselectedMap : mapResult toSelectedCut
      (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x)) =
      AspisR1SelectedMaskProbe.field.QM31.square (toSelected x) := by
    calc
      mapResult toSelectedCut
          (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x)) =
        mapResult AspisR1S9QMSquareCombinedSelectedV1.toSelectedQM
          (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x)) :=
            congrArg (fun f : XQ → SQ => mapResult f
              (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x))) hmapper.symm
      _ = AspisR1SelectedMaskProbe.field.QM31.square
          (AspisR1S9QMSquareCombinedSelectedV1.toSelectedQM (toCut x)) := hselected
      _ = AspisR1SelectedMaskProbe.field.QM31.square (toSelected x) :=
            congrArg AspisR1SelectedMaskProbe.field.QM31.square hinput
  calc
    mapResult fromCut
        (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x)) =
      mapResult (fun z : XQ => fromSelected (toSelectedCut z))
        (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x)) := by
          exact congrArg (fun f : XQ → CQ => mapResult f
            (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x))) hround
    _ = mapResult fromSelected
        (mapResult toSelectedCut
          (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x))) := by
            exact (mapResult_comp fromSelected toSelectedCut _).symm
    _ = mapResult fromSelected
        (AspisR1SelectedMaskProbe.field.QM31.square (toSelected x)) :=
          congrArg (mapResult fromSelected) hselectedMap
    _ = AspisR1S9ConcreteFieldOpsV1.actualQMSquare x := by
          unfold AspisR1S9ConcreteFieldOpsV1.actualQMSquare
          change mapResult fromSelected
              (AspisR1SelectedMaskProbe.field.QM31.square (toSelected x)) =
            (do
              let z ← AspisR1SelectedMaskProbe.field.QM31.square (toSelected x)
              Result.ok (fromSelected z))
          exact AspisR1S9SourceResultTransportV1.mapResult_eq_bind _ _


#print axioms actual_qm_square_maps_to_installed_helper

end AspisR1S9QMSquareHelperSourceBridgeV1
