import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
theorem t1 : Usize.max < UScalar.size UScalarTy.Usize := by
  first
  | (simp [Usize.max, UScalar.max, UScalar.size]; omega)
  | (unfold Usize.max UScalar.max UScalar.size; omega)
  | (have := Nat.one_le_two_pow (n := UScalarTy.Usize.numBits); simp [Usize.max, UScalar.max, UScalar.size]; omega)
theorem t2 (s : Slice Std.U8) : s.val.length ≤ Usize.max := s.property
theorem t3 : (1#usize).val = 1 := by simp
theorem t4 (i : Usize) (n : Nat) (hn : i.val < n) (hl : n ≤ Usize.max) : (i.wrapping_add 1#usize).val = i.val + 1 := by
  rw [UScalar.wrapping_add_val_eq, t3]
  apply Nat.mod_eq_of_lt
  have := t1
  omega
theorem t5 (s : Slice Std.U8) (i : Usize) (h : i.val < s.val.length) : Slice.index_usize s i = ok (s.val[i.val]'h) := by
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, h]
theorem t6 (s : Slice Std.U8) : s.len.val = s.val.length := by simp
