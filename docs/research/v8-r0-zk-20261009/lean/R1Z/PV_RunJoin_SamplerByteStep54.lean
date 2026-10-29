import R1Z.PV_RunJoin_SamplerByteIndices54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerByteStep54
open PV_RunJoin_CircleRawSampler52 PV_RunJoin_SamplerByteIndices54

theorem complete (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) (hi : i.val<8) :
    ∃ next, shipped_sampler.qm31_digits_loop0.body block rank i=
      ok (cont (next,Usize.wrapping_add i 1#usize)) := by
  let start := Usize.wrapping_mul 4#usize i
  have hv : start.val=4*i.val := mul4 i hi
  have h0 : start.val<block.val.length := by rw [block.property,hv];change 4*i.val<32;omega
  have h1 : (Usize.wrapping_add start 1#usize).val<block.val.length := by
    rw [block.property,add start 1#usize (by omega) (by decide),hv]
    change 4*i.val+1<32;omega
  have h2 : (Usize.wrapping_add start 2#usize).val<block.val.length := by
    rw [block.property,add start 2#usize (by omega) (by decide),hv]
    change 4*i.val+2<32;omega
  have h3 : (Usize.wrapping_add start 3#usize).val<block.val.length := by
    rw [block.property,add start 3#usize (by omega) (by decide),hv]
    change 4*i.val+3<32;omega
  obtain ⟨b0,r0,_⟩ := WP.spec_imp_exists (Array.index_usize_spec block start h0)
  obtain ⟨b1,r1,_⟩ := WP.spec_imp_exists (Array.index_usize_spec block (Usize.wrapping_add start 1#usize) h1)
  obtain ⟨b2,r2,_⟩ := WP.spec_imp_exists (Array.index_usize_spec block (Usize.wrapping_add start 2#usize) h2)
  obtain ⟨b3,r3,_⟩ := WP.spec_imp_exists (Array.index_usize_spec block (Usize.wrapping_add start 3#usize) h3)
  let w := core.num.U32.from_le_bytes (Array.make 4#usize [b0,b1,b2,b3])
  have hrank : i.val<rank.val.length := by rw [rank.property];exact hi
  obtain ⟨next,hwrite,_⟩ := WP.spec_imp_exists (Array.update_spec rank i w hrank)
  refine ⟨next,?_⟩
  have go : i<8#usize := hi
  unfold shipped_sampler.qm31_digits_loop0.body
  simp only [if_pos go,lift,bind_tc_ok]
  change (do
    let b0 ← Array.index_usize block start
    let b1 ← Array.index_usize block (Usize.wrapping_add start 1#usize)
    let b2 ← Array.index_usize block (Usize.wrapping_add start 2#usize)
    let b3 ← Array.index_usize block (Usize.wrapping_add start 3#usize)
    let next ← Array.update rank i (core.num.U32.from_le_bytes (Array.make 4#usize [b0,b1,b2,b3]))
    ok (cont (next,Usize.wrapping_add i 1#usize)))=ok _
  rw [r0,bind_tc_ok,r1,bind_tc_ok,r2,bind_tc_ok,r3,bind_tc_ok,hwrite,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_SamplerByteStep54
