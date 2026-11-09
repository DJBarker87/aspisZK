
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
