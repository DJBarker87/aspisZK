import S8Kani2MutableLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace S8Kani2SliceSetIndexLemmas
variable {α : Type} (s : Slice α) (i : Std.Usize) (j : Nat) (x : α)
theorem len_val_eq_length : s.len.val = s.val.length := by
  simp [Slice.len, UScalar.ofNatCore_val_eq]
theorem setAtNat_same (hi : i.val < s.len.val) (hij : i.val = j) :
    Slice.index_usize (s.setAtNat j x) i = .ok x := by
  have hjlen : j < s.len.val := by rw [← hij]; exact hi
  have hjlist : j < s.val.length := by rw [← len_val_eq_length s]; exact hjlen
  unfold Slice.index_usize Slice.setAtNat
  simp [hij, hjlist]
theorem setAtNat_ne (hi : i.val < s.len.val) (hj : j < s.len.val)
    (hij : i.val ≠ j) :
    Slice.index_usize (s.setAtNat j x) i = Slice.index_usize s i := by
  have hiList : i.val < s.val.length := by rw [← len_val_eq_length s]; exact hi
  have hjList : j < s.val.length := by rw [← len_val_eq_length s]; exact hj
  unfold Slice.index_usize Slice.setAtNat
  simp [hij, hiList, hjList]
#print axioms len_val_eq_length
#print axioms setAtNat_same
#print axioms setAtNat_ne
end S8Kani2SliceSetIndexLemmas
