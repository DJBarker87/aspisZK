import NDO_JFs_TX2_TableRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Geo18
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : domain.Point U32 := ⟨2041864042#u32,1797422629#u32⟩
theorem source0 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 63860#usize=ok value0 := by
  have ra : Array.index_usize fast_domain.TABLE_A 372#usize=ok (298013744#u32,1631477536#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[372]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 124#usize=ok (1581002989#u32,970103636#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[124]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 63860#usize &&& 511#usize=372#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 63860#usize 372#usize 124#usize
    (298013744#u32,1631477536#u32) (1581002989#u32,970103636#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 298013744 1631477536 1581002989 970103636 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 298013744 1631477536 1581002989 970103636 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=2041864042#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=1797422629#u32 := UScalar.eq_of_val_eq vy
  have same : point=value0 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source0

def value1 : domain.Point U32 := ⟨2041864042#u32,1797422629#u32⟩
theorem source1 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 63860#usize=ok value1 := source0
#print axioms source1

def value2 : domain.Point U32 := ⟨257782126#u32,288856873#u32⟩
theorem source2 : fast_domain.fibre_point R17CurrentCM31Semantics.operations 63863#usize=ok value2 := by
  have ra : Array.index_usize fast_domain.TABLE_A 375#usize=ok (91770747#u32,643271934#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_A
    change fast_domain.TABLE_A_entries[375]?=some _
    norm_num only [fast_domain.TABLE_A_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_A_chunk_00_length,fast_domain.TABLE_A_chunk_01_length,fast_domain.TABLE_A_chunk_02_length,fast_domain.TABLE_A_chunk_03_length,fast_domain.TABLE_A_chunk_04_length,fast_domain.TABLE_A_chunk_05_length,fast_domain.TABLE_A_chunk_06_length,fast_domain.TABLE_A_chunk_07_length,fast_domain.TABLE_A_chunk_08_length,fast_domain.TABLE_A_chunk_09_length,fast_domain.TABLE_A_chunk_10_length,fast_domain.TABLE_A_chunk_11_length,fast_domain.TABLE_A_chunk_12_length,fast_domain.TABLE_A_chunk_13_length,fast_domain.TABLE_A_chunk_14_length,fast_domain.TABLE_A_chunk_15_length]
    all_goals rfl
  have rb : Array.index_usize fast_domain.TABLE_B 124#usize=ok (1581002989#u32,970103636#u32) := by
    apply JFs_TX2_TableRead.source
    unfold fast_domain.TABLE_B
    change fast_domain.TABLE_B_entries[124]?=some _
    norm_num only [fast_domain.TABLE_B_entries,List.getElem?_append,List.length_append,fast_domain.TABLE_B_chunk_00_length,fast_domain.TABLE_B_chunk_01_length,fast_domain.TABLE_B_chunk_02_length,fast_domain.TABLE_B_chunk_03_length,fast_domain.TABLE_B_chunk_04_length,fast_domain.TABLE_B_chunk_05_length,fast_domain.TABLE_B_chunk_06_length,fast_domain.TABLE_B_chunk_07_length,fast_domain.TABLE_B_chunk_08_length,fast_domain.TABLE_B_chunk_09_length,fast_domain.TABLE_B_chunk_10_length,fast_domain.TABLE_B_chunk_11_length,fast_domain.TABLE_B_chunk_12_length,fast_domain.TABLE_B_chunk_13_length,fast_domain.TABLE_B_chunk_14_length,fast_domain.TABLE_B_chunk_15_length]
    all_goals rfl
  have mask : 63863#usize &&& 511#usize=375#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    all_goals rfl
  obtain ⟨point,run,vx,vy,_,_⟩ := JFs_TX2_PointCall.source 63863#usize 375#usize 124#usize
    (91770747#u32,643271934#u32) (1581002989#u32,970103636#u32) mask
    (JFs_TX2_PointShift.source _ _ (by rfl)) ra rb (by decide) (by decide)
  change point.x.val=ExtractedCurrentCM31Mul.realWord 91770747 643271934 1581002989 970103636 at vx
  change point.y.val=ExtractedCurrentCM31Mul.imagWord 91770747 643271934 1581002989 970103636 at vy
  norm_num [ExtractedCurrentCM31Mul.realWord,ExtractedCurrentCM31Mul.imagWord] at vx vy
  have ex : point.x=257782126#u32 := UScalar.eq_of_val_eq vx
  have ey : point.y=288856873#u32 := UScalar.eq_of_val_eq vy
  have same : point=value2 := by
    cases point
    exact congrArg₂ (fun x y : U32 => (⟨x,y⟩ : domain.Point U32)) ex ey
  exact same ▸ run
#print axioms source2

end AspisR1.JFs_TX2_Geo18
end
