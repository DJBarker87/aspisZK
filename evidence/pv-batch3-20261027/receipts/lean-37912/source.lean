import PV_B3_PrefixCounter222
namespace PV_B3_PrefixRank222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_222 PV_B3_PrefixCounter222
set_option autoImplicit false

theorem decrement (i : Usize) (h : 0 < i.val) :
    (Usize.wrapping_sub i 1#usize).val = i.val - 1 := by
  rw [Usize.wrapping_sub_val_eq]
  have bound : i.val < UScalar.size .Usize := i.hSize
  change (i.val + (UScalar.size .Usize - 1)) % UScalar.size .Usize = i.val - 1
  rw [show i.val + (UScalar.size .Usize - 1) = (i.val - 1) + UScalar.size .Usize from by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem decreases (point : Array Q 10#usize) (i next : Usize)
    (h : host_multilinear.sparse_eq_weights_loop0.body point i = ok (cont next)) :
    next.val < i.val := by
  obtain ⟨hi, hn⟩ := body_counter point i (cont next) h
  rw [hn, decrement i hi]
  omega

#print axioms decrement
#print axioms decreases
end PV_B3_PrefixRank222
