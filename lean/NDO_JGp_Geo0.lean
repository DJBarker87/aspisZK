import NDO_JFs_TX2_TableRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Geo0
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : domain.Point U32 := ⟨4199594#u32,98204382#u32⟩
theorem source0 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 93499#usize=ok value0 := by
  have ra : Array.index_usize fast_domain.TABLE_A 315#usize=ok (1618829578#u32,261070109#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[315]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 182#usize=ok (1834599352#u32,1895440138#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[182]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 93499#usize &&& 511#usize=315#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 93499#usize 315#usize 182#usize
    (1618829578#u32,261070109#u32) (1834599352#u32,1895440138#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 1618829578 261070109 1834599352 1895440138 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 1618829578 261070109 1834599352 1895440138 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=4199594#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=98204382#u32 := UScalar.eq_of_val_eq vy
  have same : point=value0 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source0

def value1 : domain.Point U32 := ⟨943454693#u32,1290140261#u32⟩
theorem source1 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 93496#usize=ok value1 := by
  have ra : Array.index_usize fast_domain.TABLE_A 312#usize=ok (15470579#u32,1643565293#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[312]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 182#usize=ok (1834599352#u32,1895440138#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[182]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 93496#usize &&& 511#usize=312#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 93496#usize 312#usize 182#usize
    (15470579#u32,1643565293#u32) (1834599352#u32,1895440138#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 15470579 1643565293 1834599352 1895440138 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 15470579 1643565293 1834599352 1895440138 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=943454693#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1290140261#u32 := UScalar.eq_of_val_eq vy
  have same : point=value1 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source1

def value2 : domain.Point U32 := ⟨4199594#u32,98204382#u32⟩
theorem source2 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 93499#usize=ok value2 := source0
#print axioms source2

end AspisR1.JGp_Geo0
end
