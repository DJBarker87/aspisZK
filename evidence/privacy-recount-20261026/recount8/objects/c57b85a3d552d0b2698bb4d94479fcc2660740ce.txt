import R1Z.ProverRwQueryWordTotal
import R1Z.ProverCommitQueryTotal26
set_option autoImplicit false
namespace R1Z.ProverRwQueryDecode
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan ProverRwQueryWord
open ProverRwQueryWordTotal AspisR1QueryScanUnrolled.r0_transcript

theorem read_closed (blocks : Blocks) (k draws : Usize) (bound : k.val<8) :
    readWord blocks k draws = ok (queryMaskWord (blockRankWord
      (blocks.val[k.val]'(by simpa [blocks.property] using bound)) (draws.val%8))) := by
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
  change (do
    let b0 ← Array.index_usize block (Usize.wrapping_mul 4#usize i)
    let b1 ← Array.index_usize block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 1#usize)
    let b2 ← Array.index_usize block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 2#usize)
    let b3 ← Array.index_usize block (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 3#usize)
    ok (core.num.U32.from_le_bytes (Array.make 4#usize [b0,b1,b2,b3]) &&& 262143#u32)) = ok (queryMaskWord (blockRankWord block (draws.val%8)))
  rw [h0read,h1read,h2read,h3read]
  simp only [bind_tc_ok,hm,h1,h2,h3]
  have remval : i.val=draws.val%8 := hiv
  rw [←remval]
  unfold queryMaskWord blockRankWord
  rw [dif_pos ib]
  rfl


#print axioms read_closed
end R1Z.ProverRwQueryDecode
