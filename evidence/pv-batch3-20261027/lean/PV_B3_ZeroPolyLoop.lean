import PV_B3_ZeroPolynomial
namespace PV_B3_ZeroPolyLoop
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_117 PV_B3_ZeroArithmetic PV_B3_ZeroPolynomial
set_option autoImplicit false
abbrev body := PV_B3_AuditSourceD324.Poly121.body polynomial triple prepared
abbrev pred (i : Usize) := Usize.wrapping_sub i 1#usize

theorem step (i : Usize) (hi : i.val ≤ 6) :
    body (Z,i) = ok (if 0#usize < i then cont (Z,pred i) else done Z) := by
  unfold body PV_B3_AuditSourceD324.Poly121.body
    host_arithmetic.evaluate_state_only_polynomial_loop.body
  dsimp only
  by_cases h : 0#usize < i
  · rw [if_pos h,if_pos h]
    have hp : (pred i).val ≤ 6 := by
      rw [PV_B3_PrefixRank222.decrement i h]
      omega
    simp only [lift,bind_tc_ok,prepared_mul,block _ hp,PV_B3_ZeroArithmetic.add]
  · rw [if_neg h,if_neg h]

theorem bounded : ∀ n (i : Usize), i.val = n → n ≤ 6 →
    PV_B3_BoundedLoop.bounded body n (Z,i) = ok Z := by
  intro n
  induction n with
  | zero =>
    intro i hi hn
    have h : ¬ 0#usize < i := by change ¬ 0 < i.val; omega
    rw [PV_B3_BoundedLoop.bounded,step i (by omega),if_neg h]
  | succ n ih =>
    intro i hi hn
    have h : 0#usize < i := by change 0 < i.val; omega
    have hp : (pred i).val = n := by rw [PV_B3_PrefixRank222.decrement i h]; omega
    rw [PV_B3_BoundedLoop.bounded,step i (by omega),if_pos h]
    exact ih (pred i) hp (by omega)

theorem source : host_arithmetic.evaluate_state_only_polynomial polynomial Z = ok Z := by
  rw [PV_B3_AuditSourceD324.Poly121.source_complete]
  unfold PV_B3_AuditSourceD324.Poly121.reference
  simp only [PV_B3_ZeroArithmetic.square,PV_B3_ZeroArithmetic.mul,prepare,
    triple_eq,block6,bind_tc_ok]
  exact bounded 6 6#usize rfl (by decide)

#print axioms step
#print axioms bounded
#print axioms source
end PV_B3_ZeroPolyLoop
