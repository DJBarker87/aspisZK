namespace AspisR72Sampler
namespace PCVB_R72

theorem hPv : field.P.val = 2147483647 := by unfold field.P; rfl

theorem h64 : (U64.max : Nat) = 18446744073709551615 := by scalar_tac
theorem h32 : (U32.max : Nat) = 4294967295 := by scalar_tac

set_option maxHeartbeats 400000 in
@[step] theorem add_spec (a b : field.M31) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    field.M31.add a b ⦃ r => r.val = PCVB_QM.ad a.val b.val ∧ r.val < 2147483647 ⦄ := by
  unfold field.M31.add
  step*
  all_goals (
    subst_vars
    simp only [PCVB_QM.ad, hPv, ge_iff_le, UScalar.le_equiv, h32] at *
    omega)

set_option maxHeartbeats 400000 in
@[step] theorem sub_spec (a b : field.M31) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    field.M31.sub a b ⦃ r => r.val = PCVB_QM.sb a.val b.val ∧ r.val < 2147483647 ⦄ := by
  unfold field.M31.sub
  step*
  all_goals (
    subst_vars
    simp only [PCVB_QM.sb, hPv, ge_iff_le, UScalar.le_equiv, h32] at *
    omega)

@[step] theorem dbl_spec (a : field.M31) (ha : a.val < 2147483647) :
    field.M31.double a ⦃ r => r.val = PCVB_QM.ad a.val a.val ∧ r.val < 2147483647 ⦄ := by
  unfold field.M31.double
  exact add_spec a a ha ha

@[step] theorem red_spec_G (x : Std.U64) : field.reduce_u64 x ⦃ r => r.val = x.val % 2147483647 ⦄ := by
  exact PCVB_M31.red_val_spec field.P hPv x

@[step] theorem m31red_spec (x : Std.U64) : field.M31.reduce_u64 x ⦃ r => r.val = x.val % 2147483647 ⦄ := by
  unfold field.M31.reduce_u64
  have := red_spec_G x
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists this
  rw [hr]; simp only [bind_tc_ok]
  exact (WP.spec_ok _).mpr hv

