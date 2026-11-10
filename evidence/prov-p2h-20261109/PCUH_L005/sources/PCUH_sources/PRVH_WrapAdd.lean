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
  have := Usize.size_pos
  have h2 : j.val + 1 < Std.Usize.size := by scalar_tac
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

end PRVH
#print axioms PRVH.usize_add_one_wrap
#print axioms PRVH.update_ok_lt
