import JFs_TX2_PointShift
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Geo11
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : domain.Point U32 := ⟨90208729#u32,670446566#u32⟩
theorem source0 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 218094#usize=ok value0 := by
  have ra : Array.index_usize fast_domain.TABLE_A 494#usize=ok (2083000424#u32,83400055#u32) := by
    unfold fast_domain.TABLE_A
    rfl
  have rb : Array.index_usize fast_domain.TABLE_B 425#usize=ok (569540672#u32,885330917#u32) := by
    unfold fast_domain.TABLE_B
    rfl
  have mask : 218094#usize &&& 511#usize=494#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 218094#usize 494#usize 425#usize
    (2083000424#u32,83400055#u32) (569540672#u32,885330917#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 2083000424 83400055 569540672 885330917 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 2083000424 83400055 569540672 885330917 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=90208729#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=670446566#u32 := UScalar.eq_of_val_eq vy
  have same : point=value0 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source0

def value1 : domain.Point U32 := ⟨586767722#u32,1457499478#u32⟩
theorem source1 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 218092#usize=ok value1 := by
  have ra : Array.index_usize fast_domain.TABLE_A 492#usize=ok (1031337775#u32,1391460640#u32) := by
    unfold fast_domain.TABLE_A
    rfl
  have rb : Array.index_usize fast_domain.TABLE_B 425#usize=ok (569540672#u32,885330917#u32) := by
    unfold fast_domain.TABLE_B
    rfl
  have mask : 218092#usize &&& 511#usize=492#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 218092#usize 492#usize 425#usize
    (1031337775#u32,1391460640#u32) (569540672#u32,885330917#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 1031337775 1391460640 569540672 885330917 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 1031337775 1391460640 569540672 885330917 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=586767722#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1457499478#u32 := UScalar.eq_of_val_eq vy
  have same : point=value1 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source1

def value2 : domain.Point U32 := ⟨670446566#u32,2057274918#u32⟩
theorem source2 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 218095#usize=ok value2 := by
  have ra : Array.index_usize fast_domain.TABLE_A 495#usize=ok (83400055#u32,64483223#u32) := by
    unfold fast_domain.TABLE_A
    rfl
  have rb : Array.index_usize fast_domain.TABLE_B 425#usize=ok (569540672#u32,885330917#u32) := by
    unfold fast_domain.TABLE_B
    rfl
  have mask : 218095#usize &&& 511#usize=495#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 218095#usize 495#usize 425#usize
    (83400055#u32,64483223#u32) (569540672#u32,885330917#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 83400055 64483223 569540672 885330917 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 83400055 64483223 569540672 885330917 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=670446566#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=2057274918#u32 := UScalar.eq_of_val_eq vy
  have same : point=value2 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source2

end AspisR1.JFs_TX2_Geo11
end
