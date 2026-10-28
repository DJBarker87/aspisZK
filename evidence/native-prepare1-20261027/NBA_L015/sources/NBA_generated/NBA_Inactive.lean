import NBA_Carriers
set_option autoImplicit false
namespace AspisR1.NBA_Inactive
open Aeneas Aeneas.Std Result LPi_FieldValues

theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x)=ok v) : ∃ x,m=ok x ∧ k x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem limbs (a : Array U32 8#usize) (out : NE)
    (call : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs a=ok (some out)) :
    canonE out := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs at call
  obtain ⟨w0,r0,h0⟩ := bind_success _ _ _ call
  split at h0
  · cases h0
  · rename_i c0
    obtain ⟨w1,r1,h1⟩ := bind_success _ _ _ h0
    split at h1
    · cases h1
    · rename_i c1
      obtain ⟨w2,r2,h2⟩ := bind_success _ _ _ h1
      split at h2
      · cases h2
      · rename_i c2
        obtain ⟨w3,r3,h3⟩ := bind_success _ _ _ h2
        split at h3
        · cases h3
        · rename_i c3
          obtain ⟨w4,r4,h4⟩ := bind_success _ _ _ h3
          split at h4
          · cases h4
          · rename_i c4
            obtain ⟨w5,r5,h5⟩ := bind_success _ _ _ h4
            split at h5
            · cases h5
            · rename_i c5
              obtain ⟨w6,r6,h6⟩ := bind_success _ _ _ h5
              split at h6
              · cases h6
              · rename_i c6
                obtain ⟨w7,r7,h7⟩ := bind_success _ _ _ h6
                split at h7
                · cases h7
                · rename_i c7
                  have eqn := Option.some.inj (Result.ok.inj h7)
                  subst out
                  unfold canonE canonQ canonC LPi_CMProduct.Canon
                  change ((w0.val<2147483647 ∧ w1.val<2147483647) ∧ (w2.val<2147483647 ∧ w3.val<2147483647)) ∧ ((w4.val<2147483647 ∧ w5.val<2147483647) ∧ (w6.val<2147483647 ∧ w7.val<2147483647))
                  simp only [FIo_Native.aspis_core.field.P] at c0 c1 c2 c3 c4 c5 c6 c7
                  scalar_tac

theorem bytes (b : Slice U8) (out : NE)
    (call : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b=ok (some out)) :
    canonE out := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes at call
  split at call
  · cases call
  ·
    obtain ⟨v0,read0,h0⟩ := bind_success _ _ _ call
    obtain ⟨v1,read1,h1⟩ := bind_success _ _ _ h0
    obtain ⟨v2,read2,h2⟩ := bind_success _ _ _ h1
    obtain ⟨v3,read3,h3⟩ := bind_success _ _ _ h2
    simp only [lift,bind_tc_ok] at h3
    obtain ⟨v4,read4,h4⟩ := bind_success _ _ _ h3
    obtain ⟨v5,read5,h5⟩ := bind_success _ _ _ h4
    obtain ⟨v6,read6,h6⟩ := bind_success _ _ _ h5
    obtain ⟨v7,read7,h7⟩ := bind_success _ _ _ h6
    simp only [lift,bind_tc_ok] at h7
    obtain ⟨v8,read8,h8⟩ := bind_success _ _ _ h7
    obtain ⟨v9,read9,h9⟩ := bind_success _ _ _ h8
    obtain ⟨v10,read10,h10⟩ := bind_success _ _ _ h9
    obtain ⟨v11,read11,h11⟩ := bind_success _ _ _ h10
    simp only [lift,bind_tc_ok] at h11
    obtain ⟨v12,read12,h12⟩ := bind_success _ _ _ h11
    obtain ⟨v13,read13,h13⟩ := bind_success _ _ _ h12
    obtain ⟨v14,read14,h14⟩ := bind_success _ _ _ h13
    obtain ⟨v15,read15,h15⟩ := bind_success _ _ _ h14
    simp only [lift,bind_tc_ok] at h15
    obtain ⟨v16,read16,h16⟩ := bind_success _ _ _ h15
    obtain ⟨v17,read17,h17⟩ := bind_success _ _ _ h16
    obtain ⟨v18,read18,h18⟩ := bind_success _ _ _ h17
    obtain ⟨v19,read19,h19⟩ := bind_success _ _ _ h18
    simp only [lift,bind_tc_ok] at h19
    obtain ⟨v20,read20,h20⟩ := bind_success _ _ _ h19
    obtain ⟨v21,read21,h21⟩ := bind_success _ _ _ h20
    obtain ⟨v22,read22,h22⟩ := bind_success _ _ _ h21
    obtain ⟨v23,read23,h23⟩ := bind_success _ _ _ h22
    simp only [lift,bind_tc_ok] at h23
    obtain ⟨v24,read24,h24⟩ := bind_success _ _ _ h23
    obtain ⟨v25,read25,h25⟩ := bind_success _ _ _ h24
    obtain ⟨v26,read26,h26⟩ := bind_success _ _ _ h25
    obtain ⟨v27,read27,h27⟩ := bind_success _ _ _ h26
    simp only [lift,bind_tc_ok] at h27
    obtain ⟨v28,read28,h28⟩ := bind_success _ _ _ h27
    obtain ⟨v29,read29,h29⟩ := bind_success _ _ _ h28
    obtain ⟨v30,read30,h30⟩ := bind_success _ _ _ h29
    obtain ⟨v31,read31,h31⟩ := bind_success _ _ _ h30
    simp only [lift,bind_tc_ok] at h31
    exact limbs _ out h31

#print axioms bytes
#print axioms bind_success
#print axioms limbs
end AspisR1.NBA_Inactive
