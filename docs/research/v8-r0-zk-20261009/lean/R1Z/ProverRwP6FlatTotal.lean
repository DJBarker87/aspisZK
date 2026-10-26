import R1Z.ProverRwP6ArrayRead
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6FlatTotal
open Aeneas Aeneas.Std Result ProverRwFull
theorem total (x : aspis_core.field.wide_exact.WideExact) :
    ∃ bytes, ProverRwP6FlatSource.wide_bytes_flat x = ok bytes := by
  unfold ProverRwP6FlatSource.wide_bytes_flat
    ProverRwP6FlatSource.aspis_core.field.wide_exact.WideExact.to_limbs
    ProverRwDictionaryBytes.Src.limbs
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.to_limbs
  simp only [bind_tc_ok]
  obtain ⟨v0, h0⟩ := ProverRwP6ArrayRead.read (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) 0#usize (by decide)
  rw [h0]
  simp only [bind_tc_ok, lift]
  obtain ⟨v1, h1⟩ := ProverRwP6ArrayRead.read (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) 1#usize (by decide)
  rw [h1]
  simp only [bind_tc_ok, lift]
  obtain ⟨v2, h2⟩ := ProverRwP6ArrayRead.read (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) 2#usize (by decide)
  rw [h2]
  simp only [bind_tc_ok, lift]
  obtain ⟨v3, h3⟩ := ProverRwP6ArrayRead.read (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) 3#usize (by decide)
  rw [h3]
  simp only [bind_tc_ok, lift]
  obtain ⟨v4, h4⟩ := ProverRwP6ArrayRead.read (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) 4#usize (by decide)
  rw [h4]
  simp only [bind_tc_ok, lift]
  obtain ⟨v5, h5⟩ := ProverRwP6ArrayRead.read (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) 5#usize (by decide)
  rw [h5]
  simp only [bind_tc_ok, lift]
  obtain ⟨v6, h6⟩ := ProverRwP6ArrayRead.read (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) 6#usize (by decide)
  rw [h6]
  simp only [bind_tc_ok, lift]
  obtain ⟨v7, h7⟩ := ProverRwP6ArrayRead.read (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) 7#usize (by decide)
  rw [h7]
  simp only [bind_tc_ok, lift]
  obtain ⟨v8, h8⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v0) 0#usize (by decide)
  rw [h8]
  simp only [bind_tc_ok, lift]
  obtain ⟨v9, h9⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v0) 1#usize (by decide)
  rw [h9]
  simp only [bind_tc_ok, lift]
  obtain ⟨v10, h10⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v0) 2#usize (by decide)
  rw [h10]
  simp only [bind_tc_ok, lift]
  obtain ⟨v11, h11⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v0) 3#usize (by decide)
  rw [h11]
  simp only [bind_tc_ok, lift]
  obtain ⟨v12, h12⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v1) 0#usize (by decide)
  rw [h12]
  simp only [bind_tc_ok, lift]
  obtain ⟨v13, h13⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v1) 1#usize (by decide)
  rw [h13]
  simp only [bind_tc_ok, lift]
  obtain ⟨v14, h14⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v1) 2#usize (by decide)
  rw [h14]
  simp only [bind_tc_ok, lift]
  obtain ⟨v15, h15⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v1) 3#usize (by decide)
  rw [h15]
  simp only [bind_tc_ok, lift]
  obtain ⟨v16, h16⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v2) 0#usize (by decide)
  rw [h16]
  simp only [bind_tc_ok, lift]
  obtain ⟨v17, h17⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v2) 1#usize (by decide)
  rw [h17]
  simp only [bind_tc_ok, lift]
  obtain ⟨v18, h18⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v2) 2#usize (by decide)
  rw [h18]
  simp only [bind_tc_ok, lift]
  obtain ⟨v19, h19⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v2) 3#usize (by decide)
  rw [h19]
  simp only [bind_tc_ok, lift]
  obtain ⟨v20, h20⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v3) 0#usize (by decide)
  rw [h20]
  simp only [bind_tc_ok, lift]
  obtain ⟨v21, h21⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v3) 1#usize (by decide)
  rw [h21]
  simp only [bind_tc_ok, lift]
  obtain ⟨v22, h22⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v3) 2#usize (by decide)
  rw [h22]
  simp only [bind_tc_ok, lift]
  obtain ⟨v23, h23⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v3) 3#usize (by decide)
  rw [h23]
  simp only [bind_tc_ok, lift]
  obtain ⟨v24, h24⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v4) 0#usize (by decide)
  rw [h24]
  simp only [bind_tc_ok, lift]
  obtain ⟨v25, h25⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v4) 1#usize (by decide)
  rw [h25]
  simp only [bind_tc_ok, lift]
  obtain ⟨v26, h26⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v4) 2#usize (by decide)
  rw [h26]
  simp only [bind_tc_ok, lift]
  obtain ⟨v27, h27⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v4) 3#usize (by decide)
  rw [h27]
  simp only [bind_tc_ok, lift]
  obtain ⟨v28, h28⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v5) 0#usize (by decide)
  rw [h28]
  simp only [bind_tc_ok, lift]
  obtain ⟨v29, h29⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v5) 1#usize (by decide)
  rw [h29]
  simp only [bind_tc_ok, lift]
  obtain ⟨v30, h30⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v5) 2#usize (by decide)
  rw [h30]
  simp only [bind_tc_ok, lift]
  obtain ⟨v31, h31⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v5) 3#usize (by decide)
  rw [h31]
  simp only [bind_tc_ok, lift]
  obtain ⟨v32, h32⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v6) 0#usize (by decide)
  rw [h32]
  simp only [bind_tc_ok, lift]
  obtain ⟨v33, h33⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v6) 1#usize (by decide)
  rw [h33]
  simp only [bind_tc_ok, lift]
  obtain ⟨v34, h34⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v6) 2#usize (by decide)
  rw [h34]
  simp only [bind_tc_ok, lift]
  obtain ⟨v35, h35⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v6) 3#usize (by decide)
  rw [h35]
  simp only [bind_tc_ok, lift]
  obtain ⟨v36, h36⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v7) 0#usize (by decide)
  rw [h36]
  simp only [bind_tc_ok, lift]
  obtain ⟨v37, h37⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v7) 1#usize (by decide)
  rw [h37]
  simp only [bind_tc_ok, lift]
  obtain ⟨v38, h38⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v7) 2#usize (by decide)
  rw [h38]
  simp only [bind_tc_ok, lift]
  obtain ⟨v39, h39⟩ := ProverRwP6ArrayRead.read (core.num.U32.to_le_bytes v7) 3#usize (by decide)
  rw [h39]
  simp only [bind_tc_ok, lift]
  exact ⟨_, rfl⟩
#print axioms total
end R1Z.ProverRwP6FlatTotal
