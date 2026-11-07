import LIB_FieldTransport
set_option autoImplicit false
noncomputable section
namespace LIB_VField
open Aeneas Aeneas.Std LIB_VCarriers
open LIB_VScalarCarriers (toRaw)
open AspisR1.FIp_SemanticArithmetic
abbrev qadd := LIB_VArithmetic.qadd
abbrev qmul := LIB_VArithmetic.qmul
abbrev maskValue := LIB_VMask.maskValue
/-- The adopted add dictionary at the SAME canonical four words. -/
theorem qadd_exact (x y : QM31) :
 add (toRaw x) (toRaw y) = .ok (toRaw (qadd x y)) := by
 change mapResult (AspisR1SelectedMaskProbe.field.QM31.add
  (LIB_FieldTransport.probe x) (LIB_FieldTransport.probe y)) = _
 rw [LIB_FieldTransport.add_probe x y]
 rfl
theorem qmul_exact (x y : QM31) :
 mul (toRaw x) (toRaw y) = .ok (toRaw (qmul x y)) := by
 change mapResult (AspisR1SelectedMaskProbe.field.QM31.mul
  (LIB_FieldTransport.probe x) (LIB_FieldTransport.probe y)) = _
 rw [LIB_FieldTransport.mul_probe x y]
 rfl
def c1 (c : Claims) : Array MQ 16#usize :=
 ⟨(List.finRange 16).map (fun j => toRaw (LIB_VMask.cell c ⟨j.val,by omega⟩)),by simp⟩
def maskOnly (c : Claims) : Array MQ 10#usize :=
 ⟨(List.finRange 10).map (fun j => toRaw (LIB_VMask.cell c ⟨16+j.val,by omega⟩)),by simp⟩
def g (c : Claims) : MQ := toRaw (LIB_VMask.cell c ⟨27,by omega⟩)
theorem c1_probe (c : Claims) : mapArray (c1 c) = LIB_VMask.c1 c := by
 apply Subtype.ext
 simp only [mapArray,c1,LIB_VMask.c1,List.map_map]
 rfl
theorem mask_probe (c : Claims) : mapArray (maskOnly c) = LIB_VMask.maskOnly c := by
 apply Subtype.ext
 simp only [mapArray,maskOnly,LIB_VMask.maskOnly,List.map_map]
 rfl
theorem point_probe (a : Alpha) : mapArray (alphaRaw a) = LIB_VMask.point a := by
 apply Subtype.ext
 simp only [mapArray,alphaRaw,LIB_VScalarCarriers.array,LIB_VMask.point,List.map_map]
 rfl
/-- TX1:076, exact 16+10+1 projection from claims[0], at the SAME alpha. -/
theorem mask_exact (c : Claims) (a : Alpha) :
 mask (c1 c) (maskOnly c) (g c) (alphaRaw a) = .ok (toRaw (maskValue c a)) := by
 unfold mask
 rw [c1_probe,mask_probe,point_probe]
 change mapResult (AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
  (LIB_VMask.c1 c) (LIB_VMask.maskOnly c) (LIB_VMask.g c) (LIB_VMask.point a)) = _
 rw [LIB_VMask.mask_native]
 rfl
#print axioms qadd_exact
#print axioms qmul_exact
#print axioms c1_probe
#print axioms mask_probe
#print axioms point_probe
#print axioms mask_exact
end LIB_VField
