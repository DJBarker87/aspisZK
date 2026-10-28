import NDO_JFs_TX2_TableRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Geo3
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : domain.Point U32 := ⟨741659990#u32,1452551567#u32⟩
theorem source0 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 245899#usize=ok value0 := by
  have ra : Array.index_usize fast_domain.TABLE_A 139#usize=ok (1555011007#u32,546000691#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[139]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 480#usize=ok (1168068815#u32,1631133982#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[480]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 245899#usize &&& 511#usize=139#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 245899#usize 139#usize 480#usize
    (1555011007#u32,546000691#u32) (1168068815#u32,1631133982#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 1555011007 546000691 1168068815 1631133982 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 1555011007 546000691 1168068815 1631133982 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=741659990#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1452551567#u32 := UScalar.eq_of_val_eq vy
  have same : point=value0 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source0

def value1 : domain.Point U32 := ⟨2123169078#u32,1407407520#u32⟩
theorem source1 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 245896#usize=ok value1 := by
  have ra : Array.index_usize fast_domain.TABLE_A 136#usize=ok (226919109#u32,591805476#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[136]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 480#usize=ok (1168068815#u32,1631133982#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[480]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 245896#usize &&& 511#usize=136#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 245896#usize 136#usize 480#usize
    (226919109#u32,591805476#u32) (1168068815#u32,1631133982#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 226919109 591805476 1168068815 1631133982 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 226919109 591805476 1168068815 1631133982 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=2123169078#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1407407520#u32 := UScalar.eq_of_val_eq vy
  have same : point=value1 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source1

def value2 : domain.Point U32 := ⟨741659990#u32,1452551567#u32⟩
theorem source2 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 245899#usize=ok value2 := source0
#print axioms source2

end AspisR1.JGp_Geo3
end
