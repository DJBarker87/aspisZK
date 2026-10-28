import NCO_ValidateModel
import ExtractedRecordByteCanonicality
import LPr_WordNat
set_option autoImplicit false
namespace NDF_ChunkWords
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedRecordByteCanonicality

theorem window4 (arr : Array U8 32#usize) (i : Fin 8) :
    (arr.val.drop (4*i.val)).take 4 =
      [byteAt arr ⟨4*i.val,by omega⟩,byteAt arr ⟨4*i.val+1,by omega⟩,
       byteAt arr ⟨4*i.val+2,by omega⟩,byteAt arr ⟨4*i.val+3,by omega⟩] := by
  have size : arr.val.length=32 := arr.property
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_cons,List.length_nil]
    omega
  · intro k hk hlist
    have small : k<4 := by simpa using hlist
    interval_cases k <;> simp [byteAt,List.getElem_take,List.getElem_drop]

theorem word_value (arr : Array U8 32#usize) (i : Fin 8) :
    LPl_Kit_Bytes.le32 ((arr.val.drop (4*i.val)).take 4) = (wordLE arr i).val := by
  rw [window4]
  unfold wordLE
  rw [AspisR1.LPr_WordNat.value]
  simp [LPl_Kit_Bytes.le32]
  omega

def Good (arr : Array U8 32#usize) : Prop :=
  ∀ i : Fin 8, (wordLE arr i).val<2147483647 ∧ (i.val<4 ∨ (wordLE arr i).val=0)

theorem valid_iff (arr : Array U8 32#usize) :
    LPl_Kit_Bytes.validChunk 8 true arr.val=true ↔ Good arr := by
  unfold LPl_Kit_Bytes.validChunk Good
  simp only [List.all_eq_true,List.mem_range,Bool.and_eq_true,Bool.not_true,Bool.false_or,decide_eq_true_eq]
  constructor
  · intro h i
    simpa only [word_value arr i] using h i.val i.isLt
  · intro h j hj
    simpa only [word_value arr ⟨j,hj⟩] using h ⟨j,hj⟩

#print axioms window4
#print axioms word_value
#print axioms valid_iff
end NDF_ChunkWords
