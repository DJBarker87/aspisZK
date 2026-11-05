import NJA_CountBody
import NJA_Reads

set_option autoImplicit false
namespace NJA_CountStep
open Aeneas Aeneas.Std Result ControlFlow NJA_Multiproof

theorem shift_one (x : U32) : (U32.wrapping_shr x 1#u32).val = x.val / 2 := by
  unfold U32.wrapping_shr UScalar.wrapping_shr
  change (x.val >>> (1 % 32)) = x.val / 2
  rw [Nat.shiftRight_eq_div_pow]

theorem advance (i : Usize) (hi : i.val < 16) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  change i.val + 1 < UScalar.size .Usize
  exact lt_trans (show i.val + 1 < (17#usize).val by scalar_tac) (17#usize).hSize

-- One arbitrary prestate, including both exit branches; no successful-loop premise.
theorem group_step (a : Array U32 16#usize) (n j : Usize) (p : U32)
    (hn : n.val ≤ 16) :
    multiproof.node_count_loop0_loop0_loop0.body .Two a n p j =
      if active : j < n then
        if (a.val[j.val]'(by have len : a.val.length=16 := a.property; scalar_tac)).val / 2 = p.val
        then ok (cont (Usize.wrapping_add j 1#usize)) else ok (done j)
      else ok (done j) := by
  unfold multiproof.node_count_loop0_loop0_loop0.body
  split
  next h =>
    have hj : j.val < (16#usize).val := by scalar_tac
    rw [NJA_Arity.index_result, NJA_Reads.index_ok a j hj]
    simp only [NJA_Arity.two_bits, bind_tc_ok, lift]
    have eq : U32.wrapping_shr (a.val[j.val]'(by have len : a.val.length=16 := a.property; scalar_tac)) 1#u32 = p ↔
        (a.val[j.val]'(by have len : a.val.length=16 := a.property; scalar_tac)).val/2 = p.val := by
      rw [← shift_one]
      constructor
      · exact congrArg UScalar.val
      · exact UScalar.eq_of_val_eq
    simp only [eq, if_pos h, bind_tc_ok]
  next h => simp only [if_neg h]

#print axioms shift_one
#print axioms advance
#print axioms group_step
end NJA_CountStep
