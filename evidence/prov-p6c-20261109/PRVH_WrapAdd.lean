import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

namespace PRVH

/-- the checked `j + 1` on `Usize` agrees with `wrapping_add j 1` whenever `j.val < 2^32 - 1`
(true for every index of a fixed-size array of at most 2^32 - 1 cells; here used for j < 1024). -/
theorem usize_add_one_wrap (j : Std.Usize) (h : j.val < 1024) :
    (j + 1#usize : Result Std.Usize) = ok (Std.Usize.wrapping_add j 1#usize) := by
  have hmax : j.val + (1#usize).val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := j) (y := 1#usize) hmax)
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hv, Std.Usize.wrapping_add_val_eq]
  have h1 : (1#usize).val = 1 := by scalar_tac
  rw [h1]
  have h2 : j.val + 1 < UScalar.size UScalarTy.Usize := by
    rw [h1, Std.Usize.max_def] at hmax
    rw [UScalar.size_UScalarTyUsize, Std.Usize.size_def]
    have := Nat.one_le_two_pow (n := Std.Usize.numBits)
    omega
  exact (Nat.mod_eq_of_lt h2).symm

/-- a successful `Array.update` certifies the index bound. -/
theorem update_ok_lt {α : Type _} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize) (x : α)
    (a : Std.Array α n) (h : Std.Array.update v i x = ok a) : i.val < v.length := by
  by_contra hc
  have hn : v[i]? = none := by
    rw [Std.Array.getElem?_Usize_eq]
    exact List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hc)
  unfold Std.Array.update at h
  rw [hn] at h
  simp at h


/-- checked right shift of a `Usize` by the literal `9 : I32` is the wrapping shift by `9 : U32` (the shift amount is in range). -/
theorem usize_shr9 (x : Std.Usize) : (x >>> 9#i32 : Result Std.Usize) = ok (Std.Usize.wrapping_shr x 9#u32) := by
  show UScalar.shiftRight_IScalar x 9#i32 = _
  unfold UScalar.shiftRight_IScalar
  have h9 : (9#i32).val = 9 := by decide
  simp only [h9]
  simp [UScalar.shiftRight, Std.Usize.wrapping_shr, UScalar.wrapping_shr, UScalarTy.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]


/-- `j + 1` is the wrapping increment whenever `j < i` for some `Usize` `i` (then `j + 1 ≤ i ≤ Usize.max`). -/
theorem usize_add_one_of_lt {j i : Std.Usize} (h : j < i) :
    (j + 1#usize : Result Std.Usize) = ok (Std.Usize.wrapping_add j 1#usize) := by
  have hj : j.val < i.val := h
  have hmax : j.val + (1#usize).val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := j) (y := 1#usize) hmax)
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hv, Std.Usize.wrapping_add_val_eq]
  have h1 : (1#usize).val = 1 := by scalar_tac
  rw [h1]
  have h2 : j.val + 1 < UScalar.size UScalarTy.Usize := by
    rw [h1, Std.Usize.max_def] at hmax
    rw [UScalar.size_UScalarTyUsize, Std.Usize.size_def]
    have := Nat.one_le_two_pow (n := Std.Usize.numBits)
    omega
  exact (Nat.mod_eq_of_lt h2).symm

end PRVH
#print axioms PRVH.usize_add_one_of_lt
#print axioms PRVH.usize_shr9
#print axioms PRVH.usize_add_one_wrap
#print axioms PRVH.update_ok_lt
