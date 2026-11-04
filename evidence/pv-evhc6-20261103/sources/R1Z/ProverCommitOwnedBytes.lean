import R1Z.ProverCommitOwnedTotal
import R1Z.ProverCommitOwnedWord
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result
open R0Z.FsStatement R1Z.FinalR1PBin
open R1Z.ProverCommitStreamSource (Bytes32)

def byteAt (block : Bytes32) (i : Fin 32) : U8 :=
  block.val[i.val]'(by have := block.property; change block.val.length = 32 at this; omega)

def byteWord (block : Bytes32) (j : Fin 8) : U32 :=
  core.num.U32.from_le_bytes (Aeneas.Std.Array.make 4#usize
    [byteAt block ⟨4*j.val, by omega⟩,
     byteAt block ⟨4*j.val+1, by omega⟩,
     byteAt block ⟨4*j.val+2, by omega⟩,
     byteAt block ⟨4*j.val+3, by omega⟩])

theorem index_byteAt (block : Bytes32) (i : Usize) (bound : i.val < 32) :
    Aeneas.Std.Array.index_usize block i = ok (byteAt block ⟨i.val, bound⟩) := by
  obtain ⟨x, hx, hval⟩ := WP.spec_imp_exists
    (Aeneas.Std.Array.index_usize_spec block i (by have := block.property; change block.val.length = 32 at this; change i.val < block.val.length; omega))
  exact hx.trans (congrArg Result.ok hval)

theorem offset_value (word : Usize) (bound : word.val < 8) (amount : Usize)
    (small : amount.val ≤ 3) :
    (Usize.wrapping_add (Usize.wrapping_mul word 4#usize) amount).val =
      4*word.val+amount.val := by
  rw [Usize.wrapping_add_val_eq]
  have size := usize_size_lower
  have four : (4#usize).val = 4 := by scalar_tac
  have mul : (Usize.wrapping_mul word 4#usize).val = word.val*4 := by
    rw [Usize.wrapping_mul_val_eq, four, Nat.mod_eq_of_lt (by omega)]
  rw [mul, Nat.mod_eq_of_lt (by omega)]
  omega

theorem readBlock_byteWord (block : Bytes32) (word : Usize) (bound : word.val < 8) :
    readBlock block word = ok (byteWord block ⟨word.val, bound⟩) := by
  have size := usize_size_lower
  have off : (Usize.wrapping_mul word 4#usize).val = 4*word.val := by
    rw [Usize.wrapping_mul_val_eq]
    have four : (4#usize).val = 4 := by scalar_tac
    rw [four, Nat.mod_eq_of_lt (by omega)]; omega
  have one : (1#usize).val = 1 := by scalar_tac
  have two : (2#usize).val = 2 := by scalar_tac
  have three : (3#usize).val = 3 := by scalar_tac
  have o1 := offset_value word bound 1#usize (by decide)
  have o2 := offset_value word bound 2#usize (by decide)
  have o3 := offset_value word bound 3#usize (by decide)
  simp only [readBlock, index_byteAt _ _ (by omega : (Usize.wrapping_mul word 4#usize).val < 32),
    index_byteAt _ _ (by omega : (Usize.wrapping_add (Usize.wrapping_mul word 4#usize) 1#usize).val < 32),
    index_byteAt _ _ (by omega : (Usize.wrapping_add (Usize.wrapping_mul word 4#usize) 2#usize).val < 32),
    index_byteAt _ _ (by omega : (Usize.wrapping_add (Usize.wrapping_mul word 4#usize) 3#usize).val < 32),
    bind_tc_ok, byteWord, off, o1, o2, o3, one, two, three]

#print axioms index_byteAt
#print axioms offset_value
#print axioms readBlock_byteWord
end R1Z.ProverCommitOwnedDecoder
