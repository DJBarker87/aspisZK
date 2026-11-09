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
    omega)

set_option maxHeartbeats 400000 in
@[step] theorem r23_spec (l r : Std.U64) (hl : l.val ≤ 4294967294) (hr : r.val ≤ 4294967294) :
    field.r23_product_u32_bounded l r ⦃ z => z.val = l.val * r.val ⦄ := by
  rw [PRVEq.AspisR72Sampler.Funs.field.r23_gate]
  have : l.val * r.val ≤ U64.max := by
    have := Nat.mul_le_mul hl hr
    rw [h64]; omega
  exact U64.mul_spec this

structure Can (x : field.CM31) : Prop where
  ha : x.a.val < 2147483647
  hb : x.b.val < 2147483647

@[step] theorem cm31add_spec (x y : field.CM31) (hx : Can x) (hy : Can y) :
    field.CM31.add x y ⦃ r => r.a.val = PCVB_QM.ad x.a.val y.a.val ∧ r.b.val = PCVB_QM.ad x.b.val y.b.val ∧ Can r ⦄ := by
  unfold field.CM31.add
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hya, hyb⟩ := hy
  step*
  refine ⟨by assumption, by assumption, ⟨?_, ?_⟩⟩ <;> assumption

@[step] theorem cm31sub_spec (x y : field.CM31) (hx : Can x) (hy : Can y) :
    field.CM31.sub x y ⦃ r => r.a.val = PCVB_QM.sb x.a.val y.a.val ∧ r.b.val = PCVB_QM.sb x.b.val y.b.val ∧ Can r ⦄ := by
  unfold field.CM31.sub
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hya, hyb⟩ := hy
  step*
  refine ⟨by assumption, by assumption, ⟨?_, ?_⟩⟩ <;> assumption

@[step] theorem mulr_spec (x : field.CM31) (hx : Can x) :
    field.mul_by_r x ⦃ r => r.a.val = (PCVB_QM.mulr x.a.val x.b.val).1 ∧ r.b.val = (PCVB_QM.mulr x.a.val x.b.val).2 ∧ Can r ⦄ := by
  unfold field.mul_by_r
  obtain ⟨hxa, hxb⟩ := hx
  step*
  refine ⟨?_, ?_, ⟨m1_post2, m3_post2⟩⟩
  · simp only [PCVB_QM.mulr, m1_post1, m_post1]
  · simp only [PCVB_QM.mulr, m3_post1, m2_post1]

set_option maxHeartbeats 400000 in
@[step] theorem cm31mul_spec (x y : field.CM31) (hx : Can x) (hy : Can y) :
    field.CM31.mul x y ⦃ r => r.a.val = (PCVB_QM.cmm x.a.val x.b.val y.a.val y.b.val).1 ∧
      r.b.val = (PCVB_QM.cmm x.a.val x.b.val y.a.val y.b.val).2 ∧ Can r ⦄ := by
  unfold field.CM31.mul
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hya, hyb⟩ := hy
  simp only [lift, bind_tc_ok]
  step*
  refine ⟨?_, ?_, ⟨m_post2, m4_post2⟩⟩
  · simp only [PCVB_QM.cmm, m_post1, m0_post1, m1_post1]
  · simp only [PCVB_QM.cmm, m4_post1, m3_post1, m2_post, i10_post, i4_post, i9_post,
      core.convert.num.FromU64U32.from_val_eq, m0_post1, m1_post1]

theorem U64size : UScalar.size .U64 = 18446744073709551616 := by
  rw [UScalar.size_def, UScalarTy.U64_numBits_eq]; norm_num

@[step] theorem wadd_spec (x y : Std.U64) (h : x.val + y.val < 18446744073709551616) :
    lift (core.num.U64.wrapping_add x y) ⦃ z => z.val = x.val + y.val ⦄ := by
  simp only [lift, WP.spec_ok]
  rw [core.num.U64.wrapping_add_val_eq, U64size]
  exact Nat.mod_eq_of_lt h

@[step] theorem wsub_spec (x y : Std.U64) (h : y.val ≤ x.val) :
    lift (core.num.U64.wrapping_sub x y) ⦃ z => z.val = x.val - y.val ⦄ := by
  simp only [lift, WP.spec_ok]
  rw [core.num.U64.wrapping_sub_val_eq, U64size]
  have : y.val ≤ 18446744073709551615 := by scalar_tac
  have : x.val ≤ 18446744073709551615 := by scalar_tac
  omega

@[step] theorem liftfrom_spec (x : Std.U32) :
    lift (core.convert.num.FromU64U32.from x) ⦃ z => z.val = x.val ⦄ := by
  simp only [lift, WP.spec_ok]
  exact core.convert.num.FromU64U32.from_val_eq x

theorem v2 : (2#u64 : Std.U64).val = 2 := by first | rfl | decide | simp
theorem v3 : (3#u64 : Std.U64).val = 3 := by first | rfl | decide | simp

theorem hmaskG (y : Std.U64) : (y &&& core.convert.num.FromU64U32.from field.P).val = y.val % 2147483648 := by
  rw [UScalar.val_and, core.convert.num.FromU64U32.from_val_eq, hPv,
    show (2147483647:Nat) = 2^31 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

set_option maxHeartbeats 400000 in
@[step] theorem clos_spec (c : field.r24_canonical_mul.closure) (x : Std.U64) :
    field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call c x
      ⦃ u => u.val = PCVB_QM.clos x.val ∧ u.val ≤ 10737418240 ⦄ := by
  have hx : x.val < 18446744073709551616 := by scalar_tac
  unfold field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
  simp only [lift, bind_tc_ok]
  step*
  simp only [core.num.U64.wrapping_add_val_eq, U64size, hmaskG, PCVB_QM.clos, i2_post1, PCVB_M31.hshr]
  have e0 := Nat.mod_add_div x.val 2147483648
  have hb : x.val / 2147483648 < 8589934592 := Nat.div_lt_of_lt_mul (by omega)
  have hm : x.val % 2147483648 < 2147483648 := Nat.mod_lt _ (by omega)
  have hs : (x.val % 2147483648 + x.val / 2^31) % 18446744073709551616 = x.val % 2147483648 + x.val / 2^31 := by
    apply Nat.mod_eq_of_lt; simp only [PCVB_M31.e31]; omega
  rw [hs]
  simp only [PCVB_M31.e31]
  refine ⟨trivial, ?_⟩
  omega

@[step] theorem PP_spec : field.r24_canonical_mul.PP ⦃ z => z.val = 4611686014132420609 ⦄ := by
  unfold field.r24_canonical_mul.PP
  simp only [lift, bind_tc_ok]
  step*
  simp only [U32.cast_U64_val_eq, hPv] at *
  omega

@[step] theorem new_spec (a b : field.M31) : field.CM31.new a b ⦃ r => r = { a := a, b := b } ⦄ := by
  unfold field.CM31.new
  simp only [WP.spec_ok]

structure QCan (l : field.QM31) : Prop where
  c0 : Can l.c0
  c1 : Can l.c1

theorem r24_none (l r : field.QM31)
    (h : ¬ (l.c0.a.val < 2147483647 ∧ l.c0.b.val < 2147483647 ∧ l.c1.a.val < 2147483647 ∧ l.c1.b.val < 2147483647 ∧ r.c0.a.val < 2147483647 ∧ r.c0.b.val < 2147483647 ∧ r.c1.a.val < 2147483647 ∧ r.c1.b.val < 2147483647)) :
    field.r24_canonical_mul l r = ok none := by
  unfold field.r24_canonical_mul
  by_cases c1 : l.c0.a ≥ field.P
  · simp only [c1, ↓reduceIte]
  by_cases c2 : l.c0.b ≥ field.P
  · simp only [c1, c2, ↓reduceIte]
  by_cases c3 : l.c1.a ≥ field.P
  · simp only [c1, c2, c3, ↓reduceIte]
  by_cases c4 : l.c1.b ≥ field.P
  · simp only [c1, c2, c3, c4, ↓reduceIte]
  by_cases c5 : r.c0.a ≥ field.P
  · simp only [c1, c2, c3, c4, c5, ↓reduceIte]
  by_cases c6 : r.c0.b ≥ field.P
  · simp only [c1, c2, c3, c4, c5, c6, ↓reduceIte]
  by_cases c7 : r.c1.a ≥ field.P
  · simp only [c1, c2, c3, c4, c5, c6, c7, ↓reduceIte]
  by_cases c8 : r.c1.b ≥ field.P
  · simp only [c1, c2, c3, c4, c5, c6, c7, c8, ↓reduceIte]
  exfalso
  apply h
  simp only [ge_iff_le, UScalar.le_equiv, hPv, not_le] at *
  omega

set_option maxHeartbeats 1000000 in
theorem r24_canon (l r : field.QM31) (h1 : l.c0.a.val < 2147483647) (h2 : l.c0.b.val < 2147483647) (h3 : l.c1.a.val < 2147483647) (h4 : l.c1.b.val < 2147483647) (h5 : r.c0.a.val < 2147483647) (h6 : r.c0.b.val < 2147483647) (h7 : r.c1.a.val < 2147483647) (h8 : r.c1.b.val < 2147483647) :
    field.r24_canonical_mul l r ⦃ o => ∃ res, o = some res ∧
      res.c0.a.val = (PCVB_QM.gateQ l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val).1 ∧
      res.c0.b.val = (PCVB_QM.gateQ l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val).2.1 ∧
      res.c1.a.val = (PCVB_QM.gateQ l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val).2.2.1 ∧
      res.c1.b.val = (PCVB_QM.gateQ l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val).2.2.2 ⦄ := by
  have hprod : ∀ x y : field.M31, x.val < 2147483647 → y.val < 2147483647 → x.val * y.val ≤ 4611686009837453316 := by
    intro x y hx hy
    have := Nat.mul_le_mul (show x.val ≤ 2147483646 by omega) (show y.val ≤ 2147483646 by omega)
    omega
  have p00 := hprod l.c0.a r.c0.a h1 h5
  have p01 := hprod l.c0.a r.c0.b h1 h6
  have p02 := hprod l.c0.a r.c1.a h1 h7
  have p03 := hprod l.c0.a r.c1.b h1 h8
  have p10 := hprod l.c0.b r.c0.a h2 h5
  have p11 := hprod l.c0.b r.c0.b h2 h6
  have p12 := hprod l.c0.b r.c1.a h2 h7
  have p13 := hprod l.c0.b r.c1.b h2 h8
  have p20 := hprod l.c1.a r.c0.a h3 h5
  have p21 := hprod l.c1.a r.c0.b h3 h6
  have p22 := hprod l.c1.a r.c1.a h3 h7
  have p23 := hprod l.c1.a r.c1.b h3 h8
  have p30 := hprod l.c1.b r.c0.a h4 h5
  have p31 := hprod l.c1.b r.c0.b h4 h6
  have p32 := hprod l.c1.b r.c1.a h4 h7
  have p33 := hprod l.c1.b r.c1.b h4 h8
  have n1 : ¬ (l.c0.a ≥ field.P) := by
    rw [ge_iff_le, UScalar.le_equiv, hPv]; omega
  have n2 : ¬ (l.c0.b ≥ field.P) := by
    rw [ge_iff_le, UScalar.le_equiv, hPv]; omega
  have n3 : ¬ (l.c1.a ≥ field.P) := by
    rw [ge_iff_le, UScalar.le_equiv, hPv]; omega
  have n4 : ¬ (l.c1.b ≥ field.P) := by
    rw [ge_iff_le, UScalar.le_equiv, hPv]; omega
  have n5 : ¬ (r.c0.a ≥ field.P) := by
    rw [ge_iff_le, UScalar.le_equiv, hPv]; omega
  have n6 : ¬ (r.c0.b ≥ field.P) := by
    rw [ge_iff_le, UScalar.le_equiv, hPv]; omega
  have n7 : ¬ (r.c1.a ≥ field.P) := by
    rw [ge_iff_le, UScalar.le_equiv, hPv]; omega
  have n8 : ¬ (r.c1.b ≥ field.P) := by
    rw [ge_iff_le, UScalar.le_equiv, hPv]; omega
  unfold field.r24_canonical_mul
  simp only [n1, n2, n3, n4, n5, n6, n7, n8, ↓reduceIte]
  step*
  all_goals first
    | decide
    | (subst_vars; (try simp only [U32.cast_U64_val_eq, h64, Nat.le_eq, hPv, v2, v3, PCVB_QM.clos] at *); omega)
    | skip
  subst_vars
  refine ⟨{ c0 := { a := out0, b := out1 }, c1 := { a := out2, b := out3 } }, rfl, ?_, ?_, ?_, ?_⟩
  all_goals (
    simp only [PCVB_QM.gateQ, PCVB_QM.clos, U32.cast_U64_val_eq, hPv, v2, v3, Nat.le_eq, h64] at *
    omega)

set_option maxHeartbeats 1000000 in
theorem chain_spec (l r : field.QM31) (hl0 : Can l.c0) (hl1 : Can l.c1) (hr0 : Can r.c0) (hr1 : Can r.c1) :
    (do let m0 ← field.CM31.mul l.c0 r.c0
        let m1 ← field.CM31.mul l.c1 r.c1
        let c ← field.CM31.add l.c0 l.c1
        let c1 ← field.CM31.add r.c0 r.c1
        let m2 ← field.CM31.mul c c1
        let c2 ← field.mul_by_r m1
        let c3 ← field.CM31.add m0 c2
        let c4 ← field.CM31.sub m2 m0
        let c5 ← field.CM31.sub c4 m1
        ok ({ c0 := c3, c1 := c5 } : field.QM31)) ⦃ res =>
      res.c0.a.val = (PCVB_QM.qmul l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val).1 ∧ res.c0.b.val = (PCVB_QM.qmul l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val).2.1 ∧
      res.c1.a.val = (PCVB_QM.qmul l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val).2.2.1 ∧ res.c1.b.val = (PCVB_QM.qmul l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val).2.2.2 ⦄ := by
  step*
  simp only [PCVB_QM.qmul, *, and_self]

set_option maxHeartbeats 1000000 in
theorem qm31_mul_gate_eq_fresh (l r : field.QM31)
    (h1 : l.c0.a.val < 2147483647) (h2 : l.c0.b.val < 2147483647) (h3 : l.c1.a.val < 2147483647) (h4 : l.c1.b.val < 2147483647)
    (h5 : r.c0.a.val < 2147483647) (h6 : r.c0.b.val < 2147483647) (h7 : r.c1.a.val < 2147483647) (h8 : r.c1.b.val < 2147483647) :
    ∃ res, field.r24_canonical_mul l r = ok (some res) ∧
      (do let m0 ← field.CM31.mul l.c0 r.c0
          let m1 ← field.CM31.mul l.c1 r.c1
          let c ← field.CM31.add l.c0 l.c1
          let c1 ← field.CM31.add r.c0 r.c1
          let m2 ← field.CM31.mul c c1
          let c2 ← field.mul_by_r m1
          let c3 ← field.CM31.add m0 c2
          let c4 ← field.CM31.sub m2 m0
          let c5 ← field.CM31.sub c4 m1
          ok ({ c0 := c3, c1 := c5 } : field.QM31)) = ok res := by
  obtain ⟨o, hres, res, ho, v0, v1, v2, v3⟩ := WP.spec_imp_exists (r24_canon l r h1 h2 h3 h4 h5 h6 h7 h8)
  obtain ⟨y, hy, w0, w1, w2, w3⟩ := WP.spec_imp_exists (chain_spec l r ⟨h1, h2⟩ ⟨h3, h4⟩ ⟨h5, h6⟩ ⟨h7, h8⟩)
  have e0 := PCVB_QM.comp0 l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val h1 h2 h3 h4 h5 h6 h7 h8
  have e1 := PCVB_QM.comp1 l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val h1 h2 h3 h4 h5 h6 h7 h8
  have e2 := PCVB_QM.comp2 l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val h1 h2 h3 h4 h5 h6 h7 h8
  have e3 := PCVB_QM.comp3 l.c0.a.val l.c0.b.val l.c1.a.val l.c1.b.val r.c0.a.val r.c0.b.val r.c1.a.val r.c1.b.val h1 h2 h3 h4 h5 h6 h7 h8
  subst ho
  refine ⟨res, hres, ?_⟩
  rw [hy]
  have hr : res = y := by
    obtain ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ := res
    obtain ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ := y
    simp only at v0 v1 v2 v3 w0 w1 w2 w3
    have ea : a1 = a2 := UScalar.eq_imp _ _ (by rw [v0, w0, e0])
    have eb : b1 = b2 := UScalar.eq_imp _ _ (by rw [v1, w1, e1])
    have ec : c1 = c2 := UScalar.eq_imp _ _ (by rw [v2, w2, e2])
    have ed : d1 = d2 := UScalar.eq_imp _ _ (by rw [v3, w3, e3])
    subst ea eb ec ed
    rfl
  rw [hr]

end PCVB_R72
end AspisR72Sampler

set_option maxHeartbeats 1000000 in
/-- P3b: fresh QM31.mul = gate QM31.mul as functions on ALL inputs. The gate first runs r24_canonical_mul: if any of the eight
    limbs is >= P it returns none and the gate runs the same Karatsuba chain as fresh (r24_none); otherwise it returns
    some result, and r24_canon + chain_spec + comp0..3 prove that result equals the chain output limb by limb. -/
theorem PRVEq.AspisR72Sampler.Funs.field.QM31.mul : @AspisR72Sampler.PRVFresh_AspisR72Sampler_Funs.field.QM31.mul = @AspisR72Sampler.field.QM31.mul := by
  funext l r
  delta AspisR72Sampler.PRVFresh_AspisR72Sampler_Funs.field.QM31.mul AspisR72Sampler.field.QM31.mul
  simp only [PRVEq.AspisR72Sampler.Funs.field.CM31.add, PRVEq.AspisR72Sampler.Funs.field.CM31.sub,
    PRVEq.AspisR72Sampler.Funs.field.CM31.mul, PRVEq.AspisR72Sampler.Funs.field.mul_by_r]
  by_cases hc : (l.c0.a.val < 2147483647 ∧ l.c0.b.val < 2147483647 ∧ l.c1.a.val < 2147483647 ∧ l.c1.b.val < 2147483647 ∧
      r.c0.a.val < 2147483647 ∧ r.c0.b.val < 2147483647 ∧ r.c1.a.val < 2147483647 ∧ r.c1.b.val < 2147483647)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hc
    obtain ⟨res, hres, hch⟩ := AspisR72Sampler.PCVB_R72.qm31_mul_gate_eq_fresh l r h1 h2 h3 h4 h5 h6 h7 h8
    rw [hres]
    simp only [bind_tc_ok]
    exact hch
  · rw [AspisR72Sampler.PCVB_R72.r24_none l r hc]
    simp only [bind_tc_ok]
#print axioms PRVEq.AspisR72Sampler.Funs.field.QM31.mul
