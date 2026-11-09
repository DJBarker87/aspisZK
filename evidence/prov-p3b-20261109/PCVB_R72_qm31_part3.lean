
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
