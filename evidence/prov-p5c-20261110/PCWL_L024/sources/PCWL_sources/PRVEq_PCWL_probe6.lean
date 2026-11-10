import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
theorem t1 (i : Usize) (n : Nat) (hn : i.val < n) (hl : n ≤ Usize.max) : i.val + 1 < UScalar.size UScalarTy.Usize := by
  first
  | scalar_tac
  | (simp_bounds; omega)
  | (rw [UScalar.size_UScalarTyUsize]; scalar_tac)
theorem t3 : (1#usize).val = 1 := by simp
theorem t4 (i : Usize) (n : Nat) (hn : i.val < n) (hl : n ≤ Usize.max) : (i.wrapping_add 1#usize).val = i.val + 1 := by
  have h := UScalar.wrapping_add_val_eq i 1#usize
  rw [t3] at h
  rw [h]
  apply Nat.mod_eq_of_lt
  exact t1 i n hn hl
theorem t5 (s : Slice Std.U8) (i : Usize) (h : i.val < s.val.length) : Slice.index_usize s i = ok (s.val[i.val]'h) := by
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, h]
theorem t6 (s : Slice Std.U8) : s.len.val = s.val.length := by simp
