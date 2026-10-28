import PV_B3_ZeroArithmetic
import PV_B3_LinearsFinite
namespace PV_B3_ZeroLinears
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_117 PV_B3_ZeroArithmetic
set_option autoImplicit false
abbrev point := Array.repeat 10#usize Z
abbrev pred (i : Usize) := Usize.wrapping_sub i 1#usize

theorem body (i : Usize) (hi : i.val ≤ 10) :
    PV_B3_LinearsFinite.body point (Z,Z,i) =
      ok (if 0#usize < i then cont (Z,Z,pred i) else done (Z,Z)) := by
  unfold PV_B3_LinearsFinite.body host_arithmetic.selected_mask_linears_loop.body
  dsimp only
  by_cases h : 0#usize < i
  · rw [if_pos h,if_pos h]
    have hp : (pred i).val < (10#usize).val := by
      rw [PV_B3_PrefixRank222.decrement i h]
      change i.val-1 < 10
      change 0 < i.val at h
      omega
    simp only [lift,bind_tc_ok,index_repeat _ _ _ hp,PV_B3_ZeroArithmetic.add]
    split <;> rfl
  · rw [if_neg h,if_neg h]

theorem bounded : ∀ n (i : Usize), i.val = n → n ≤ 10 →
    PV_B3_BoundedLoop.bounded (PV_B3_LinearsFinite.body point) n (Z,Z,i) = ok (Z,Z) := by
  intro n
  induction n with
  | zero =>
    intro i hi hn
    have h : ¬ 0#usize < i := by change ¬ 0 < i.val; omega
    rw [PV_B3_BoundedLoop.bounded, body i (by omega), if_neg h]
  | succ n ih =>
    intro i hi hn
    have h : 0#usize < i := by change 0 < i.val; omega
    have hp : (pred i).val = n := by rw [PV_B3_PrefixRank222.decrement i h]; omega
    rw [PV_B3_BoundedLoop.bounded, body i (by omega), if_pos h]
    exact ih (pred i) hp (by omega)

theorem loop (i : Usize) (hi : i.val ≤ 10) :
    host_arithmetic.selected_mask_linears_loop point Z Z i = ok (Z,Z) := by
  rw [PV_B3_LinearsFinite.source]
  exact bounded i.val i rfl hi

theorem source : host_arithmetic.selected_mask_linears point = ok (Z,Z) := by
  unfold host_arithmetic.selected_mask_linears
  rw [loop _ (by decide)]
  simp only [bind_tc_ok,scale3,scale22,scale275,scale150,PV_B3_ZeroArithmetic.add]

#print axioms body
#print axioms bounded
#print axioms loop
#print axioms source
end PV_B3_ZeroLinears
