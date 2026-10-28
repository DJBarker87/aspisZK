import R1Z.ProverRwQueryWord

/-! Bounded byte-read totality, proved symbolically over arbitrary blocks. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryWordTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan ProverRwQueryWord

theorem offset_mul (i : Usize) (bound : i.val<8) :
    (Usize.wrapping_mul 4#usize i).val=4*i.val := by
  rw [Usize.wrapping_mul_val_eq]
  have four : (4#usize).val=4 := rfl
  rw [four,Nat.mod_eq_of_lt]
  have big := (32#usize).hSize
  change 32 < UScalar.size .Usize at big
  omega

theorem offset_add (i b : Usize) (bound : i.val<8) (hb : b.val≤3) :
    (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) b).val=4*i.val+b.val := by
  rw [Usize.wrapping_add_val_eq,offset_mul i bound,Nat.mod_eq_of_lt]
  have big := (32#usize).hSize
  change 32 < UScalar.size .Usize at big
  omega

theorem division_total (draws : Usize) (bound : draws.val<64) :
    ∃ k, (draws / 8#usize : Result Usize)=ok k ∧ k.val<8 := by
  obtain ⟨k,hk,hv⟩ := UScalar.div_spec draws (y := 8#usize) (by decide)
  refine ⟨k,hk,?_⟩
  have eight : (8#usize).val=8 := rfl
  rw [eight] at hv
  omega

theorem read_total (blocks : Blocks) (k draws : Usize) (bound : k.val<8) :
    ∃ candidate, readWord blocks k draws=ok candidate := by
  obtain ⟨i,hi,hiv⟩ := WP.spec_imp_exists (UScalar.rem_spec draws (y := 8#usize) (by decide))
  have eight : (8#usize).val=8 := rfl
  rw [eight] at hiv
  have ib : i.val<8 := by omega
  have hk := ProverCommitArrayIndex25.array_index_usize_ok blocks k (by exact bound)
  let block := blocks.val[k.val]'(by simpa [blocks.property] using bound)
  have hm := offset_mul i ib
  have h1 := offset_add i 1#usize ib (by decide)
  have h2 := offset_add i 2#usize ib (by decide)
  have h3 := offset_add i 3#usize ib (by decide)
  have h0read := ProverCommitArrayIndex25.array_index_usize_ok block (Usize.wrapping_mul 4#usize i) (by change _<32; omega)
  have h1read := ProverCommitArrayIndex25.array_index_usize_ok block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 1#usize) (by change _<32; rw [h1]; change 4*i.val+1<32; omega)
  have h2read := ProverCommitArrayIndex25.array_index_usize_ok block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 2#usize) (by change _<32; rw [h2]; change 4*i.val+2<32; omega)
  have h3read := ProverCommitArrayIndex25.array_index_usize_ok block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 3#usize) (by change _<32; rw [h3]; change 4*i.val+3<32; omega)
  simp only [readWord,hi,bind_tc_ok,lift,hk]
  change ∃ candidate, (do
    let b0 ← Array.index_usize block (Usize.wrapping_mul 4#usize i)
    let b1 ← Array.index_usize block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 1#usize)
    let b2 ← Array.index_usize block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 2#usize)
    let b3 ← Array.index_usize block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 3#usize)
    ok (core.num.U32.from_le_bytes (Array.make 4#usize [b0,b1,b2,b3]) &&& 262143#u32)) = ok candidate
  rw [h0read,h1read,h2read,h3read]
  exact ⟨_,rfl⟩

#print axioms offset_mul
#print axioms offset_add
#print axioms division_total
#print axioms read_total
end R1Z.ProverRwQueryWordTotal
