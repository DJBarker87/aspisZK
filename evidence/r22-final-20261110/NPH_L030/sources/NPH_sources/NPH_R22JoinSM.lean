import NPH_R22Towers
import RPz7_FIp_SemanticArithmetic
import RPv_EqualityValueSlice
import RPv_PoseidonPreparedSum3Source
import RPv_AspisR1_PoseidonPreparedProductCells

/-! NPH_ (R22, run of 2026-11-10 evening, step C): SelectedMaskProbe (SM) sites from the
tightened screen NPH_SITES.json (NPH_sites_scan2.py). W is limbs ≤ P; SM_WC/SM_WQ are W on
the SM CM31/QM31 carriers (NPH_R22Towers). An array is W when every successful read of it
is W (`ArrW`).
- In-family definitions not covered by NPH_R22Towers: the PreparedQm31Multiplier new/mul
  closures and bodies (mul needs only a W right operand: the stored components enter
  M31.mul alone, which is total), RPv_EqualityValueSlice QM31.sub, state_only_hiding
  cm31_mul_i/cm31_mul_r/mul_tower_basis (every coordinate < 4, and `column &&& 3` < 4),
  mask_power_26, and one iteration of each state_only_hiding loop body that calls a kernel
  (selected_mask_linears_loop, state_only_selected_mask_value_loop0/loop1 via
  mul_tower_basis, loop2), plus the straight-line tails of selected_mask_linears and
  state_only_selected_mask_value.
- Outside sites: FIp_SemanticArithmetic add/mul (W in, ok W out); PoseidonPreparedProductCells
  rightBuilder and the qm31_sum_products3_prepared_loop0 step (W right operand); and the
  karatsuba reconstruction qm31_from_karatsuba_channel_sums with its closure, which is ok
  with W output for EVERY input (the three limbs pass reduce_u64 first).
Each statement is a site statement: every kernel call at the site receives W arguments and
is ok with W output, given the stated W facts on the site's own inputs. Where those inputs
come from (the caller contexts) is listed in NPH_SITES.json and is NOT discharged here
except for the karatsuba site. Standard axioms; no ops interface or merged module changes. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22JoinSM
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies AspisR1.NPH_R22Weak AspisR1.NPH_R22Towers

abbrev ArrW {n : Usize} (a : Array AspisR1SelectedMaskProbe.field.QM31 n) : Prop :=
  ∀ k q, Array.index_usize a k = ok q → SM_WQ q

theorem add_w (x y : U32) (hx : x.val ≤ 2147483647) (hy : y.val ≤ 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.add x y = ok z ∧ z.val ≤ 2147483647 := by
  rw [SM_M31_add_eq]; exact refAdd_weak x y hx hy
theorem sub_w (x y : U32) (hx : x.val ≤ 2147483647) (hy : y.val ≤ 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.sub x y = ok z ∧ z.val ≤ 2147483647 := by
  rw [SM_M31_sub_eq]; exact refSub_weak x y hx hy

theorem idx3 {α : Type} [Inhabited α] (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) :
    ∃ t, Array.index_usize a i = ok t := by
  have hl : a.val.length = 3 := by first | exact a.property | simpa using a.property
  obtain ⟨t, ht, _⟩ := WP.spec_imp_exists (Array.index_usize_spec a i (by first | scalar_tac | (simp [hl]; omega) | simp [hl, hi] | omega))
  exact ⟨t, ht⟩

/-! ### PreparedQm31Multiplier -/

theorem PM_new_closure_ok (c : AspisR1SelectedMaskProbe.field.CM31) (hc : SM_WC c) :
    ∃ a, AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call () c = ok a := by
  obtain ⟨m, hm, _⟩ := add_w c.a c.b hc.1 hc.2
  exact ⟨_, by simp only [AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call, hm, bind_tc_ok]⟩

theorem PM_new_ok (v : AspisR1SelectedMaskProbe.field.QM31) (hv : SM_WQ v) :
    ∃ p, AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new v = ok p := by
  obtain ⟨a, ha⟩ := PM_new_closure_ok v.c0 hv.1
  obtain ⟨a1, ha1⟩ := PM_new_closure_ok v.c1 hv.2
  obtain ⟨c, hc, wc⟩ := SM_CM31_add_weak v.c0 v.c1 hv.1 hv.2
  obtain ⟨a2, ha2⟩ := PM_new_closure_ok c wc
  exact ⟨_, by simp only [AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new, ha, ha1, hc, ha2, bind_tc_ok]⟩

theorem PM_mul_closure_W (left : Array U32 3#usize) (right : AspisR1SelectedMaskProbe.field.CM31) (hr : SM_WC right) :
    ∃ z, AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call () (left, right) = ok z ∧ SM_WC z := by
  obtain ⟨l0, h0⟩ := idx3 left 0#usize (by decide)
  obtain ⟨l1, h1⟩ := idx3 left 1#usize (by decide)
  obtain ⟨l2, h2⟩ := idx3 left 2#usize (by decide)
  obtain ⟨m0, hm0, vm0⟩ := SM_M31_mul_lt l0 right.a
  obtain ⟨m11, hm11, vm11⟩ := SM_M31_mul_lt l1 right.b
  obtain ⟨m3, hm3, vm3⟩ := add_w right.a right.b hr.1 hr.2
  obtain ⟨m21, hm21, vm21⟩ := SM_M31_mul_lt l2 m3
  obtain ⟨m4, hm4, vm4⟩ := sub_w m0 m11 vm0 vm11
  obtain ⟨m5, hm5, vm5⟩ := sub_w m21 m0 vm21 vm0
  obtain ⟨m6, hm6, vm6⟩ := sub_w m5 m11 vm5 vm11
  refine ⟨({ a := m4, b := m6 } : AspisR1SelectedMaskProbe.field.CM31), ?_, vm4, vm6⟩
  simp only [AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
    h0, h1, h2, hm0, hm11, hm3, hm21, hm4, hm5, hm6, bind_tc_ok]

/-- PreparedQm31Multiplier.mul: ok and W for ANY prepared value and a W right operand. -/
theorem PM_mul_W (p : AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier) (rhs : AspisR1SelectedMaskProbe.field.QM31)
    (h : SM_WQ rhs) : ∃ z, AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul p rhs = ok z ∧ SM_WQ z := by
  obtain ⟨a, ha⟩ := idx3 p.components 0#usize (by decide)
  obtain ⟨a1, ha1⟩ := idx3 p.components 1#usize (by decide)
  obtain ⟨a2, ha2⟩ := idx3 p.components 2#usize (by decide)
  obtain ⟨m0, hm0, w0⟩ := PM_mul_closure_W a rhs.c0 h.1
  obtain ⟨m1, hm1, w1⟩ := PM_mul_closure_W a1 rhs.c1 h.2
  obtain ⟨c, hc, wc⟩ := SM_CM31_add_weak rhs.c0 rhs.c1 h.1 h.2
  obtain ⟨m2, hm2, w2⟩ := PM_mul_closure_W a2 c wc
  obtain ⟨c1, hc1, wc1⟩ := SM_mul_by_r_weak m1 w1
  obtain ⟨c2, hc2, wc2⟩ := SM_CM31_add_weak m0 c1 w0 wc1
  obtain ⟨c3, hc3, wc3⟩ := SM_CM31_sub_weak m2 m0 w2 w0
  obtain ⟨c4, hc4, wc4⟩ := SM_CM31_sub_weak c3 m1 wc3 w1
  refine ⟨({ c0 := c2, c1 := c4 } : AspisR1SelectedMaskProbe.field.QM31), ?_, wc2, wc4⟩
  simp only [AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul, ha, ha1, ha2, hm0, hm1, hc, hm2,
    hc1, hc2, hc3, hc4, bind_tc_ok]

/-- RPv_EqualityValueSlice QM31.sub. -/
theorem QM31_sub_W (a b : AspisR1SelectedMaskProbe.field.QM31) (ha : SM_WQ a) (hb : SM_WQ b) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.sub a b = ok z ∧ SM_WQ z := by
  obtain ⟨c, hc, wc⟩ := SM_CM31_sub_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, wc1⟩ := SM_CM31_sub_weak a.c1 b.c1 ha.2 hb.2
  exact ⟨({ c0 := c, c1 := c1 } : AspisR1SelectedMaskProbe.field.QM31),
    by simp only [AspisR1SelectedMaskProbe.field.QM31.sub, hc, hc1, bind_tc_ok], wc, wc1⟩

/-! ### state_only_hiding -/

theorem mul_i_W (v : AspisR1SelectedMaskProbe.field.CM31) (hv : SM_WC v) :
    ∃ z, AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_i v = ok z ∧ SM_WC z := by
  obtain ⟨m, hm, vm⟩ := SM_M31_neg_weak v.b hv.2
  exact ⟨({ a := m, b := v.a } : AspisR1SelectedMaskProbe.field.CM31),
    by simp only [AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_i, AspisR1SelectedMaskProbe.field.CM31.new, hm, bind_tc_ok], vm, hv.1⟩

theorem mul_r_W (v : AspisR1SelectedMaskProbe.field.CM31) (hv : SM_WC v) :
    ∃ z, AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r v = ok z ∧ SM_WC z := by
  obtain ⟨m, hm, vm⟩ := SM_M31_double_weak v.a hv.1
  obtain ⟨m1, hm1, vm1⟩ := sub_w m v.b vm hv.2
  obtain ⟨m2, hm2, vm2⟩ := SM_M31_double_weak v.b hv.2
  obtain ⟨m3, hm3, vm3⟩ := add_w v.a m2 hv.1 vm2
  exact ⟨({ a := m1, b := m3 } : AspisR1SelectedMaskProbe.field.CM31),
    by simp only [AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r, AspisR1SelectedMaskProbe.field.CM31.new, hm, hm1, hm2, hm3, bind_tc_ok], vm1, vm3⟩

theorem basis_W (q : AspisR1SelectedMaskProbe.field.QM31) (i : Usize) (hq : SM_WQ q) (hi : i.val < 4) :
    ∃ z, AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis q i = ok z ∧ SM_WQ z := by
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hc with h | h | h | h
  · exact ⟨q, by unfold AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis; simp only [h], hq⟩
  · obtain ⟨c, hc, wc⟩ := mul_i_W q.c0 hq.1
    obtain ⟨c1, hc1, wc1⟩ := mul_i_W q.c1 hq.2
    exact ⟨({ c0 := c, c1 := c1 } : AspisR1SelectedMaskProbe.field.QM31),
      by unfold AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis; simp only [h, hc, hc1, bind_tc_ok], wc, wc1⟩
  · obtain ⟨c, hc, wc⟩ := mul_r_W q.c1 hq.2
    exact ⟨({ c0 := c, c1 := q.c0 } : AspisR1SelectedMaskProbe.field.QM31),
      by unfold AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis; simp only [h, hc, bind_tc_ok], wc, hq.1⟩
  · obtain ⟨c, hc, wc⟩ := mul_r_W q.c1 hq.2
    obtain ⟨c1, hc1, wc1⟩ := mul_i_W c wc
    obtain ⟨c2, hc2, wc2⟩ := mul_i_W q.c0 hq.1
    exact ⟨({ c0 := c1, c1 := c2 } : AspisR1SelectedMaskProbe.field.QM31),
      by unfold AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis; simp only [h, hc, hc1, hc2, bind_tc_ok], wc1, wc2⟩

theorem and3_lt (u : Usize) : (u &&& 3#usize).val < 4 := by
  rw [UScalar.val_and]
  have h := Nat.and_le_right (n := u.val) (m := (3#usize).val)
  have h5 : (3#usize).val = 3 := by first | rfl | simp | scalar_tac
  omega

/-- Loop0/loop1 bodies: the basis transform of a read of a W array at `column &&& 3`. -/
theorem coeff_site (c1 : Array AspisR1SelectedMaskProbe.field.QM31 16#usize) (hc : ArrW c1)
    (column : Usize) (q : AspisR1SelectedMaskProbe.field.QM31) (hr : Array.index_usize c1 column = ok q) :
    ∃ z, AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis q (column &&& 3#usize) = ok z ∧ SM_WQ z :=
  basis_W q _ (hc column q hr) (and3_lt column)

theorem power26_W (v : AspisR1SelectedMaskProbe.field.QM31) (hv : SM_WQ v) :
    ∃ z, AspisR1SelectedMaskProbe.state_only_hiding.mask_power_26 v = ok z ∧ SM_WQ z := by
  obtain ⟨x2, h2, w2⟩ := SM_QM31_square_weak v hv
  obtain ⟨x4, h4, w4⟩ := SM_QM31_square_weak x2 w2
  obtain ⟨x8, h8, w8⟩ := SM_QM31_square_weak x4 w4
  obtain ⟨x16, h16, w16⟩ := SM_QM31_square_weak x8 w8
  obtain ⟨q, hq, wq⟩ := SM_QM31_mul_weak x16 x8 w16 w8
  obtain ⟨z, hz, wz⟩ := SM_QM31_mul_weak q x2 wq w2
  exact ⟨z, by simp only [AspisR1SelectedMaskProbe.state_only_hiding.mask_power_26, h2, h4, h8, h16, hq, hz, bind_tc_ok], wz⟩

/-- selected_mask_linears_loop.body, one iteration on a W state and a W point array. -/
theorem linears_body_site (point : Array AspisR1SelectedMaskProbe.field.QM31 10#usize) (hp : ArrW point)
    (suffix weighted : AspisR1SelectedMaskProbe.field.QM31) (hs : SM_WQ suffix) (hw : SM_WQ weighted)
    (k : Usize) (q : AspisR1SelectedMaskProbe.field.QM31) (hr : Array.index_usize point k = ok q) :
    ∃ s1, AspisR1SelectedMaskProbe.field.QM31.add suffix q = ok s1 ∧ SM_WQ s1 ∧
      ∃ w1, AspisR1SelectedMaskProbe.field.QM31.add weighted s1 = ok w1 ∧ SM_WQ w1 := by
  obtain ⟨s1, h1, w1⟩ := SM_QM31_add_weak suffix q hs (hp k q hr)
  obtain ⟨t, ht, wt⟩ := SM_QM31_add_weak weighted s1 hw w1
  exact ⟨s1, h1, w1, t, ht, wt⟩

theorem zero_WQ : SM_WQ AspisR1SelectedMaskProbe.field.QM31.ZERO := by
  unfold SM_WQ SM_WC AspisR1SelectedMaskProbe.field.QM31.ZERO; first | decide | simp | (refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp)
theorem one_WQ : SM_WQ AspisR1SelectedMaskProbe.field.QM31.ONE := by
  unfold SM_WQ SM_WC AspisR1SelectedMaskProbe.field.QM31.ONE; first | decide | simp | (refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp)

/-- selected_mask_linears tail on the loop's W outputs (mul_m31 is total). -/
theorem linears_tail (suffix weighted : AspisR1SelectedMaskProbe.field.QM31) :
    ∃ q q1 q2 q3 q4 q5, AspisR1SelectedMaskProbe.field.QM31.mul_m31 suffix 3#u32 = ok q ∧
      AspisR1SelectedMaskProbe.field.QM31.mul_m31 weighted 22#u32 = ok q1 ∧
      AspisR1SelectedMaskProbe.field.QM31.add q q1 = ok q2 ∧ SM_WQ q2 ∧
      AspisR1SelectedMaskProbe.field.QM31.mul_m31 suffix 275#u32 = ok q3 ∧
      AspisR1SelectedMaskProbe.field.QM31.mul_m31 weighted 150#u32 = ok q4 ∧
      AspisR1SelectedMaskProbe.field.QM31.add q3 q4 = ok q5 ∧ SM_WQ q5 := by
  obtain ⟨q, h, w⟩ := SM_QM31_mul_m31_weak suffix 3#u32
  obtain ⟨q1, h1, w1⟩ := SM_QM31_mul_m31_weak weighted 22#u32
  obtain ⟨q2, h2, w2⟩ := SM_QM31_add_weak q q1 w w1
  obtain ⟨q3, h3, w3⟩ := SM_QM31_mul_m31_weak suffix 275#u32
  obtain ⟨q4, h4, w4⟩ := SM_QM31_mul_m31_weak weighted 150#u32
  obtain ⟨q5, h5, w5⟩ := SM_QM31_add_weak q3 q4 w3 w4
  exact ⟨q, q1, q2, q3, q4, q5, h, h1, h2, w2, h3, h4, h5, w5⟩

/-- state_only_selected_mask_value_loop2.body, one iteration. -/
theorem loop2_body_site (coefficients : Array AspisR1SelectedMaskProbe.field.QM31 27#usize) (hc : ArrW coefficients)
    (p : AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier) (shared : AspisR1SelectedMaskProbe.field.QM31)
    (hs : SM_WQ shared) :
    ∃ q, AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul p shared = ok q ∧ SM_WQ q ∧
      ∀ e q1, Array.index_usize coefficients e = ok q1 →
        ∃ s1, AspisR1SelectedMaskProbe.field.QM31.add q q1 = ok s1 ∧ SM_WQ s1 := by
  obtain ⟨q, hq, wq⟩ := PM_mul_W p shared hs
  exact ⟨q, hq, wq, fun e q1 hr => SM_QM31_add_weak q q1 wq (hc e q1 hr)⟩

/-- state_only_selected_mask_value: the prepare and the tail after the loops. -/
theorem mask_tail_sites (linear explicit_linear explicit_g shared1 : AspisR1SelectedMaskProbe.field.QM31)
    (hl : SM_WQ linear) (he : SM_WQ explicit_linear) (hg : SM_WQ explicit_g) (hs : SM_WQ shared1) :
    (∃ p, AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new linear = ok p) ∧
    ∃ q q1 q2 z, AspisR1SelectedMaskProbe.state_only_hiding.mask_power_26 explicit_linear = ok q ∧
      AspisR1SelectedMaskProbe.field.QM31.add AspisR1SelectedMaskProbe.field.QM31.ONE q = ok q1 ∧
      AspisR1SelectedMaskProbe.field.QM31.mul q1 explicit_g = ok q2 ∧
      AspisR1SelectedMaskProbe.field.QM31.add shared1 q2 = ok z ∧ SM_WQ z := by
  refine ⟨PM_new_ok linear hl, ?_⟩
  obtain ⟨q, h, w⟩ := power26_W explicit_linear he
  obtain ⟨q1, h1, w1⟩ := SM_QM31_add_weak _ q one_WQ w
  obtain ⟨q2, h2, w2⟩ := SM_QM31_mul_weak q1 explicit_g w1 hg
  obtain ⟨z, hz, wz⟩ := SM_QM31_add_weak shared1 q2 hs w2
  exact ⟨q, q1, q2, z, h, h1, h2, hz, wz⟩

/-! ### Outside sites -/

theorem FIp_add_W (x y : AspisR1.FIp_SemanticArithmetic.MQ)
    (hx : SM_WQ (AspisR1.FIp_SemanticArithmetic.toProbe x)) (hy : SM_WQ (AspisR1.FIp_SemanticArithmetic.toProbe y)) :
    ∃ z, AspisR1.FIp_SemanticArithmetic.add x y = ok z ∧ SM_WQ (AspisR1.FIp_SemanticArithmetic.toProbe z) := by
  obtain ⟨w, hw, vw⟩ := SM_QM31_add_weak _ _ hx hy
  exact ⟨_, by simp only [AspisR1.FIp_SemanticArithmetic.add, hw, AspisR1.FIp_SemanticArithmetic.mapResult], vw⟩

theorem FIp_mul_W (x y : AspisR1.FIp_SemanticArithmetic.MQ)
    (hx : SM_WQ (AspisR1.FIp_SemanticArithmetic.toProbe x)) (hy : SM_WQ (AspisR1.FIp_SemanticArithmetic.toProbe y)) :
    ∃ z, AspisR1.FIp_SemanticArithmetic.mul x y = ok z ∧ SM_WQ (AspisR1.FIp_SemanticArithmetic.toProbe z) := by
  obtain ⟨w, hw, vw⟩ := SM_QM31_mul_weak _ _ hx hy
  exact ⟨_, by simp only [AspisR1.FIp_SemanticArithmetic.mul, hw, AspisR1.FIp_SemanticArithmetic.mapResult], vw⟩

theorem rightBuilder_ok (q : AspisR1SelectedMaskProbe.field.QM31) (hq : SM_WQ q) :
    ∃ z, AspisR1.PoseidonPreparedProductCells.rightBuilder q = ok z := by
  obtain ⟨s, hs, ws⟩ := SM_CM31_add_weak q.c0 q.c1 hq.1 hq.2
  obtain ⟨m0, h0, _⟩ := add_w q.c0.a q.c0.b hq.1.1 hq.1.2
  obtain ⟨m1, h1, _⟩ := add_w q.c1.a q.c1.b hq.2.1 hq.2.2
  obtain ⟨m2, h2, _⟩ := add_w s.a s.b ws.1 ws.2
  exact ⟨_, by simp only [AspisR1.PoseidonPreparedProductCells.rightBuilder, hs, h0, h1, h2, bind_tc_ok]⟩

/-- qm31_sum_products3_prepared_loop0, the kernel calls of one step on a W right entry. -/
theorem sum3_step_site (q : AspisR1SelectedMaskProbe.field.QM31) (hq : SM_WQ q) :
    ∃ s m m1 m2, AspisR1SelectedMaskProbe.field.CM31.add q.c0 q.c1 = ok s ∧
      AspisR1SelectedMaskProbe.field.M31.add q.c0.a q.c0.b = ok m ∧
      AspisR1SelectedMaskProbe.field.M31.add q.c1.a q.c1.b = ok m1 ∧
      AspisR1SelectedMaskProbe.field.M31.add s.a s.b = ok m2 := by
  obtain ⟨s, hs, ws⟩ := SM_CM31_add_weak q.c0 q.c1 hq.1 hq.2
  obtain ⟨m0, h0, _⟩ := add_w q.c0.a q.c0.b hq.1.1 hq.1.2
  obtain ⟨m1, h1, _⟩ := add_w q.c1.a q.c1.b hq.2.1 hq.2.2
  obtain ⟨m2, h2, _⟩ := add_w s.a s.b ws.1 ws.2
  exact ⟨s, m0, m1, m2, hs, h0, h1, h2⟩

theorem reduce_lt (x : U64) : ∃ y, AspisR1SelectedMaskProbe.field.M31.reduce_u64 x = ok y ∧ y.val ≤ 2147483647 := by
  obtain ⟨y, hy, vy, _⟩ := SM_reduce_u64_R22 x
  exact ⟨y, by simp only [AspisR1SelectedMaskProbe.field.M31.reduce_u64, hy, bind_tc_ok], by omega⟩

/-- Karatsuba channel closure: ok with W output for EVERY input. -/
theorem karatsuba_closure_W (t : Array U64 3#usize) :
    ∃ z, AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () t = ok z ∧ SM_WC z := by
  obtain ⟨i, hi⟩ := idx3 t 0#usize (by decide)
  obtain ⟨i1, hi1⟩ := idx3 t 1#usize (by decide)
  obtain ⟨i2, hi2⟩ := idx3 t 2#usize (by decide)
  obtain ⟨m0, h0, v0⟩ := reduce_lt i
  obtain ⟨m1, h1, v1⟩ := reduce_lt i1
  obtain ⟨m2, h2, v2⟩ := reduce_lt i2
  obtain ⟨m, hm, vm⟩ := sub_w m0 m1 v0 v1
  obtain ⟨m3, hm3, vm3⟩ := sub_w m2 m0 v2 v0
  obtain ⟨m4, hm4, vm4⟩ := sub_w m3 m1 vm3 v1
  refine ⟨({ a := m, b := m4 } : AspisR1SelectedMaskProbe.field.CM31), ?_, vm, vm4⟩
  simp only [AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    hi, hi1, hi2, h0, h1, h2, hm, hm3, hm4, bind_tc_ok]

/-- Karatsuba reconstruction: ok with W output for EVERY sums array. -/
theorem karatsuba_W (sums : Array (Array U64 3#usize) 3#usize) :
    ∃ z, AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums sums = ok z ∧ SM_WQ z := by
  obtain ⟨a, ha⟩ := idx3 sums 0#usize (by decide)
  obtain ⟨a1, ha1⟩ := idx3 sums 1#usize (by decide)
  obtain ⟨a2, ha2⟩ := idx3 sums 2#usize (by decide)
  obtain ⟨m0, h0, w0⟩ := karatsuba_closure_W a
  obtain ⟨m1, h1, w1⟩ := karatsuba_closure_W a1
  obtain ⟨m2, h2, w2⟩ := karatsuba_closure_W a2
  obtain ⟨c, hc, wc⟩ := SM_mul_by_r_weak m1 w1
  obtain ⟨c1, hc1, wc1⟩ := SM_CM31_add_weak m0 c w0 wc
  obtain ⟨c2, hc2, wc2⟩ := SM_CM31_sub_weak m2 m0 w2 w0
  obtain ⟨c3, hc3, wc3⟩ := SM_CM31_sub_weak c2 m1 wc2 w1
  refine ⟨({ c0 := c1, c1 := c3 } : AspisR1SelectedMaskProbe.field.QM31), ?_, wc1, wc3⟩
  simp only [AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums, ha, ha1, ha2, h0, h1, h2,
    hc, hc1, hc2, hc3, bind_tc_ok]

#print axioms add_w
#print axioms sub_w
#print axioms idx3
#print axioms PM_new_closure_ok
#print axioms PM_new_ok
#print axioms PM_mul_closure_W
#print axioms PM_mul_W
#print axioms QM31_sub_W
#print axioms mul_i_W
#print axioms mul_r_W
#print axioms basis_W
#print axioms and3_lt
#print axioms coeff_site
#print axioms power26_W
#print axioms linears_body_site
#print axioms zero_WQ
#print axioms one_WQ
#print axioms linears_tail
#print axioms loop2_body_site
#print axioms mask_tail_sites
#print axioms FIp_add_W
#print axioms FIp_mul_W
#print axioms rightBuilder_ok
#print axioms sum3_step_site
#print axioms reduce_lt
#print axioms karatsuba_closure_W
#print axioms karatsuba_W
end AspisR1.NPH_R22JoinSM
