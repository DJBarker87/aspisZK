import LIB_VCarriers
set_option autoImplicit false
noncomputable section
namespace LIB_VMask
open Aeneas Aeneas.Std LIB_VCarriers
open LIB_VScalarCarriers (toRaw NQ array)
abbrev PQ := AspisR1SelectedMaskProbe.field.QM31
abbrev Canon := AspisR1.ExtractedMaskCallerModel.CanonicalQM
def toProbe (q : QM31) : PQ := AspisR1.FIp_SemanticArithmetic.toProbe (toRaw q)
def fromProbe (q : PQ) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem probe_canonical (q : QM31) : Canon (toProbe q) := q.property
/-- Row zero's SAME 16+10+1 words, as read by r1_semantic.rs. -/
def cell (c : Claims) (i : Fin 29) : QM31 :=
 (c.val[0]'(by have h:=c.property;change c.val.length=3 at h;omega)).val[i.val]'(by
  have h:=(c.val[0]'(by have h:=c.property;change c.val.length=3 at h;omega)).property
  change _ = 29 at h
  omega)
def c1 (c : Claims) : Array PQ 16#usize :=
 ⟨(List.finRange 16).map (fun j => toProbe (cell c ⟨j.val,by omega⟩)),by simp⟩
def maskOnly (c : Claims) : Array PQ 10#usize :=
 ⟨(List.finRange 10).map (fun j => toProbe (cell c ⟨16+j.val,by omega⟩)),by simp⟩
def g (c : Claims) : PQ := toProbe (cell c ⟨27,by omega⟩)
def point (a : Alpha) : Array PQ 10#usize := array toProbe a
theorem c1_canonical (c : Claims) (j : Fin 16) :
 Canon (AspisR1.ExtractedMaskCoefficientStep.c1Cell (c1 c) j) := by
 unfold AspisR1.ExtractedMaskCoefficientStep.c1Cell c1
 simp only [List.getElem_map,List.getElem_finRange]
 exact probe_canonical _
theorem mask_canonical (c : Claims) (j : Fin 10) :
 Canon (AspisR1.ExtractedMaskCoefficientStep.maskCell (maskOnly c) j) := by
 unfold AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly
 simp only [List.getElem_map,List.getElem_finRange]
 exact probe_canonical _
theorem point_canonical (a : Alpha) (i : Nat) (hi : i<10) :
 Canon (AspisR1.ExtractedMaskLinearLoop.pointAtNat (point a) i hi) := by
 unfold AspisR1.ExtractedMaskLinearLoop.pointAtNat point array
 simp only [List.getElem_map]
 exact probe_canonical _
theorem total (c : Claims) (a : Alpha) :
 ∃ out : PQ,
 AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
  (c1 c) (maskOnly c) (g c) (point a) = .ok out ∧ Canon out := by
 obtain ⟨out,run,canonical,_⟩ := AspisR1.NHU_Mask.result
  (c1 c) (maskOnly c) (g c) (point a)
  (c1_canonical c) (mask_canonical c) (point_canonical a) (probe_canonical _)
 exact ⟨out,run,canonical⟩
def maskValue (c : Claims) (a : Alpha) : QM31 :=
 ⟨fromProbe (Classical.choose (total c a)),(Classical.choose_spec (total c a)).2⟩
theorem mask_native (c : Claims) (a : Alpha) :
 AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
  (c1 c) (maskOnly c) (g c) (point a) = .ok (toProbe (maskValue c a)) :=
 (Classical.choose_spec (total c a)).1
#print axioms probe_canonical
#print axioms c1_canonical
#print axioms mask_canonical
#print axioms point_canonical
#print axioms total
#print axioms mask_native
end LIB_VMask
