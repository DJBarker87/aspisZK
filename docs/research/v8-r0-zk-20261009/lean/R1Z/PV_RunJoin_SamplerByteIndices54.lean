import R1Z.PV_RunJoin_SamplerCounters54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerByteIndices54

theorem size : 4294967296≤UScalar.size .Usize := by
  rw [UScalar.size_def]
  exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits

theorem mul4 (i : Usize) (hi : i.val<8) :
    (Usize.wrapping_mul 4#usize i).val=4*i.val := by
  rw [Usize.wrapping_mul_val_eq]
  change (4*i.val)%UScalar.size .Usize=4*i.val
  exact Nat.mod_eq_of_lt (by have h := size;omega)

theorem add (i j : Usize) (hi : i.val<32) (hj : j.val<4) :
    (Usize.wrapping_add i j).val=i.val+j.val := by
  rw [Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt (by have h := size;omega)

#print axioms size
#print axioms mul4
#print axioms add
end R1Z.PV_RunJoin_SamplerByteIndices54
