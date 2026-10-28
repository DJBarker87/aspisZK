import R1Z.PV_RDEA_ActualNameLoop
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEA_ActualDigitTable

def table : Array Str 16#usize := Array.make 16#usize [
          toStr "0" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "1" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "2" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "3" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "4" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "5" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]),
          toStr "6" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "7" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "8" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "9" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "a" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "b" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]),
          toStr "c" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "d" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "e" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "f" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits])
          ]

theorem one_byte (bs : ByteArray) (h : bs.size=1) : bs.toList.length=1 := by
  unfold ByteArray.toList
  rw [ByteArray.toList.loop]
  simp only [h,Nat.zero_lt_succ,if_true]
  rw [ByteArray.toList.loop]
  simp only [h,Nat.lt_irrefl,if_false,List.length_reverse,List.length_cons,List.length_nil]

theorem entry_length (i : Fin 16) : (table.val[i.val]'(by have h:=i.isLt; change i.val<16; exact h)).val.length=1 := by
  fin_cases i <;> simp only [table,Array.make,List.getElem_cons_zero,List.getElem_cons_succ,toStr,List.length_map]
  all_goals apply one_byte; rw [String.size_toByteArray]; rfl

#print toStr
#print Array.make
#print Array.index_usize
#print Slice.index_usize
#print axioms one_byte
#print axioms entry_length
end R1Z.PV_RDEA_ActualDigitTable
