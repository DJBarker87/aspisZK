import S3S9ConcreteFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConcreteSquareSemanticsV1

local instance currentFieldOpsForSemantics :
    AspisR1S9HelperP6.FieldOps :=
  AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps

abbrev Q := AspisR1S9ConcreteFieldOpsV1.Q
abbrev Sem := AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics

private def toSelectedQM (x : Q) : AspisR1SelectedMaskProbe.field.QM31 :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private def fromSelectedQM (x : AspisR1SelectedMaskProbe.field.QM31) : Q :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private theorem current_canonical_iff_selected (x : Q) :
    Sem.canonical x ↔
      AspisR1.ExtractedMaskQM31SquareExact.CanonicalQM
        (toSelectedQM x) := by
  cases x with
  | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl

private theorem selected_decode_eq_current (x : Q) :
    AspisR1.ExtractedMaskQM31SquareExact.decode
        (toSelectedQM x) = Sem.decode x := by
  cases x with
  | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl

private theorem selected_roundtrip_back (x : AspisR1SelectedMaskProbe.field.QM31) :
    toSelectedQM (fromSelectedQM x) = x := by
  cases x with
  | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem concrete_qmSquare_total (x : Q) (hx : Sem.canonical x) :
    ∃ z,
      @AspisR1S9HelperP6.FieldOps.qmSquare
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x = .ok z ∧
      Sem.canonical z ∧ Sem.decode z = Sem.decode x * Sem.decode x := by
  have hxSelected := current_canonical_iff_selected x |>.mp hx
  obtain ⟨w,hw,hcan,hdecode⟩ :=
    AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact
      (toSelectedQM x) hxSelected
  refine ⟨fromSelectedQM w, ?_, ?_, ?_⟩
  · rw [AspisR1S9ConcreteFieldOpsV1.concrete_qmSquare_dispatch]
    unfold AspisR1S9ConcreteFieldOpsV1.actualQMSquare
    change (do
      let z ← AspisR1SelectedMaskProbe.field.QM31.square (toSelectedQM x)
      ok (fromSelectedQM z)) = .ok (fromSelectedQM w)
    rw [hw]
    rfl
  · apply (current_canonical_iff_selected _).mpr
    rw [selected_roundtrip_back]
    exact hcan
  · calc
      Sem.decode (fromSelectedQM w) =
          AspisR1.ExtractedMaskQM31SquareExact.decode
            (toSelectedQM (fromSelectedQM w)) :=
        (selected_decode_eq_current (fromSelectedQM w)).symm
      _ = AspisR1.ExtractedMaskQM31SquareExact.decode w := by
        rw [selected_roundtrip_back]
      _ = AspisR1.ExtractedMaskQM31SquareExact.decode (toSelectedQM x) *
          AspisR1.ExtractedMaskQM31SquareExact.decode (toSelectedQM x) := hdecode
      _ = Sem.decode x * Sem.decode x := by rw [selected_decode_eq_current]

#print axioms concrete_qmSquare_total

end AspisR1S9ConcreteSquareSemanticsV1
