import JFs_TX2_PointShift
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Geo10
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : domain.Point U32 := ⟨774039344#u32,1196781258#u32⟩
theorem source0 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 132355#usize=ok value0 := by
  have ra : Array.index_usize fast_domain.TABLE_A 259#usize=ok (693913202#u32,845241313#u32) := by
    unfold fast_domain.TABLE_A
    rfl
  have rb : Array.index_usize fast_domain.TABLE_B 258#usize=ok (100684459#u32,1640456458#u32) := by
    unfold fast_domain.TABLE_B
    rfl
  have mask : 132355#usize &&& 511#usize=259#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 132355#usize 259#usize 258#usize
    (693913202#u32,845241313#u32) (100684459#u32,1640456458#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 693913202 845241313 100684459 1640456458 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 693913202 845241313 100684459 1640456458 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord,ExtractedCurrentReducerOps.P] at vx vy
  have ex : point.x=774039344#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1196781258#u32 := UScalar.eq_of_val_eq vy
  have same : point=value0 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source0

def value1 : domain.Point U32 := ⟨1426229895#u32,1009968845#u32⟩
theorem source1 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 132352#usize=ok value1 := by
  have ra : Array.index_usize fast_domain.TABLE_A 256#usize=ok (785785922#u32,1967683322#u32) := by
    unfold fast_domain.TABLE_A
    rfl
  have rb : Array.index_usize fast_domain.TABLE_B 258#usize=ok (100684459#u32,1640456458#u32) := by
    unfold fast_domain.TABLE_B
    rfl
  have mask : 132352#usize &&& 511#usize=256#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 132352#usize 256#usize 258#usize
    (785785922#u32,1967683322#u32) (100684459#u32,1640456458#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 785785922 1967683322 100684459 1640456458 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 785785922 1967683322 100684459 1640456458 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord,ExtractedCurrentReducerOps.P] at vx vy
  have ex : point.x=1426229895#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1009968845#u32 := UScalar.eq_of_val_eq vy
  have same : point=value1 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source1

def value2 : domain.Point U32 := ⟨774039344#u32,1196781258#u32⟩
theorem source2 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 132355#usize=ok value2 := source0
#print axioms source2

end AspisR1.JFs_TX2_Geo10
end
