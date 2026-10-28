import NDO_JFs_TX2_TableRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Geo1
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : domain.Point U32 := ⟨294074545#u32,1230260130#u32⟩
theorem source0 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 147529#usize=ok value0 := by
  have ra : Array.index_usize fast_domain.TABLE_A 73#usize=ok (1823771499#u32,303108049#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[73]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 288#usize=ok (1421883301#u32,1767600112#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[288]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 147529#usize &&& 511#usize=73#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 147529#usize 73#usize 288#usize
    (1823771499#u32,303108049#u32) (1421883301#u32,1767600112#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 1823771499 303108049 1421883301 1767600112 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 1823771499 303108049 1421883301 1767600112 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=294074545#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1230260130#u32 := UScalar.eq_of_val_eq vy
  have same : point=value0 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source0

def value1 : domain.Point U32 := ⟨917223517#u32,294074545#u32⟩
theorem source1 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 147528#usize=ok value1 := by
  have ra : Array.index_usize fast_domain.TABLE_A 72#usize=ok (1844375598#u32,1823771499#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[72]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 288#usize=ok (1421883301#u32,1767600112#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[288]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 147528#usize &&& 511#usize=72#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 147528#usize 72#usize 288#usize
    (1844375598#u32,1823771499#u32) (1421883301#u32,1767600112#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 1844375598 1823771499 1421883301 1767600112 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 1844375598 1823771499 1421883301 1767600112 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=917223517#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=294074545#u32 := UScalar.eq_of_val_eq vy
  have same : point=value1 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source1

def value2 : domain.Point U32 := ⟨1076484827#u32,125351885#u32⟩
theorem source2 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 147531#usize=ok value2 := by
  have ra : Array.index_usize fast_domain.TABLE_A 75#usize=ok (1302232773#u32,1110615388#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[75]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 288#usize=ok (1421883301#u32,1767600112#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[288]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 147531#usize &&& 511#usize=75#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 147531#usize 75#usize 288#usize
    (1302232773#u32,1110615388#u32) (1421883301#u32,1767600112#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 1302232773 1110615388 1421883301 1767600112 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 1302232773 1110615388 1421883301 1767600112 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=1076484827#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=125351885#u32 := UScalar.eq_of_val_eq vy
  have same : point=value2 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source2

end AspisR1.JGp_Geo1
end
