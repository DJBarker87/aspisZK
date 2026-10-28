import NDO_JFs_TX2_TableRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Geo5
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : domain.Point U32 := ⟨170513503#u32,1893994276#u32⟩
theorem source0 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 192317#usize=ok value0 := by
  have ra : Array.index_usize fast_domain.TABLE_A 317#usize=ok (1692335411#u32,747729946#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[317]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 375#usize=ok (1683233817#u32,1287709593#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[375]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 192317#usize &&& 511#usize=317#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 192317#usize 317#usize 375#usize
    (1692335411#u32,747729946#u32) (1683233817#u32,1287709593#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 1692335411 747729946 1683233817 1287709593 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 1692335411 747729946 1683233817 1287709593 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=170513503#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1893994276#u32 := UScalar.eq_of_val_eq vy
  have same : point=value0 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source0

def value1 : domain.Point U32 := ⟨253489371#u32,170513503#u32⟩
theorem source1 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 192316#usize=ok value1 := by
  have ra : Array.index_usize fast_domain.TABLE_A 316#usize=ok (1399753701#u32,1692335411#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[316]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 375#usize=ok (1683233817#u32,1287709593#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[375]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 192316#usize &&& 511#usize=316#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 192316#usize 316#usize 375#usize
    (1399753701#u32,1692335411#u32) (1683233817#u32,1287709593#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 1399753701 1692335411 1683233817 1287709593 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 1399753701 1692335411 1683233817 1287709593 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=253489371#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=170513503#u32 := UScalar.eq_of_val_eq vy
  have same : point=value1 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source1

def value2 : domain.Point U32 := ⟨1908538125#u32,493020858#u32⟩
theorem source2 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 192319#usize=ok value2 := by
  have ra : Array.index_usize fast_domain.TABLE_A 319#usize=ok (950473072#u32,997410738#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[319]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 375#usize=ok (1683233817#u32,1287709593#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[375]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 192319#usize &&& 511#usize=319#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 192319#usize 319#usize 375#usize
    (950473072#u32,997410738#u32) (1683233817#u32,1287709593#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 950473072 997410738 1683233817 1287709593 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 950473072 997410738 1683233817 1287709593 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=1908538125#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=493020858#u32 := UScalar.eq_of_val_eq vy
  have same : point=value2 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source2

end AspisR1.JGp_Geo5
end
