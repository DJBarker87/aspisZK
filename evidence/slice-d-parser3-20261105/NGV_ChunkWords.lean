import NGO_ValidatorCallback
import NGO_ValidatorWindows
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ChunkWords
open AspisR1PrefixAggregateParser
noncomputable def words (bs : Slice U8) (size : bs.val.length=32) : Array U32 8#usize :=
 Array.make 8#usize ((List.finRange 8).map fun j =>
  core.num.U32.from_le_bytes (NGO_ValidatorWindows.block bs.val (4*j.val) (by omega))) (by simp)
theorem parse (bs : Slice U8) (size : bs.val.length=32) :
 field.wide_exact.WideExact.from_le_bytes bs =
 field.wide_exact.WideExact.from_limbs (words bs size) := by
 have len : Slice.len bs=32#usize := UScalar.eq_of_val_eq size
 simp only [field.wide_exact.WideExact.from_le_bytes,
   field.wide_exact.WideExact.BYTE_LEN,len,bne_self_eq_false,Bool.false_eq_true,if_false]
 simp [Slice.index_usize,words,NGO_ValidatorWindows.block,Array.make,size,lift]
 rfl
#print axioms parse
end NGV_ChunkWords
