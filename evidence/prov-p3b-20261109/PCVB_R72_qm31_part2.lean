
set_option maxHeartbeats 400000 in
@[step] theorem m31mul_spec (a b : field.M31) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    field.M31.mul a b ⦃ r => r.val = PCVB_QM.mm a.val b.val ∧ r.val < 2147483647 ⦄ := by
  rw [← PRVEq.AspisR72Sampler.Funs.field.M31.mul]
  unfold AspisR72Sampler.PRVFresh_AspisR72Sampler_Funs.field.M31.mul
  rw [PRVEq.AspisR72Sampler.Funs.field.reduce_u64]
  have hprod : a.val * b.val ≤ 4611686014132420609 := by
    have := Nat.mul_le_mul (show a.val ≤ 2147483646 by omega) (show b.val ≤ 2147483646 by omega)
    omega
  step*
  all_goals (
    subst_vars
    simp only [U32.cast_U64_val_eq, h64, PCVB_QM.mm] at *
    trace_state
    omega)

set_option maxHeartbeats 400000 in
@[step] theorem r23_spec (l r : Std.U64) (hl : l.val ≤ 4294967294) (hr : r.val ≤ 4294967294) :
    field.r23_product_u32_bounded l r ⦃ z => z.val = l.val * r.val ⦄ := by
  rw [PRVEq.AspisR72Sampler.Funs.field.r23_gate]
  have : l.val * r.val ≤ U64.max := by
    have := Nat.mul_le_mul hl hr
    rw [h64]; omega
  exact U64.mul_spec this
