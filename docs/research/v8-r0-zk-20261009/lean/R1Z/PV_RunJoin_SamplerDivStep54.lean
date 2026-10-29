import R1Z.PV_RunJoin_SamplerCounters54
import R1Z.PV_RunJoin_SamplerDivWord54
import R1Z.PV_RunJoin_CircleNeutralWide53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerDivStep54
open PV_RunJoin_SamplerCounters54

theorem complete (rank : Array U32 8#usize) (remainder : U64) (j : Usize)
    (hj : 0<j.val) (bound : j.val≤8) :
    ∃ next rem,
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop.body rank remainder j=
        ok (cont (next,rem,Usize.wrapping_sub j 1#usize)) ∧ rem.val<2147483647 := by
  let at1 := Usize.wrapping_sub j 1#usize
  have hat : at1.val<rank.val.length := by
    rw [rank.property]
    have h := sub_one j hj
    change at1.val<8
    unfold at1
    omega
  obtain ⟨limb,hread,_⟩ := WP.spec_imp_exists (Array.index_usize_spec rank at1 hat)
  let dividend := U64.wrapping_shl remainder 32#u32 ||| UScalar.cast .U64 limb
  obtain ⟨q,rem,hq,hr,hrem⟩ := PV_RunJoin_SamplerDivWord54.complete dividend
  obtain ⟨next,hupdate,_⟩ := WP.spec_imp_exists (Array.update_spec rank at1 (UScalar.cast .U32 q) hat)
  refine ⟨next,rem,?_,hrem⟩
  have go : j>0#usize := hj
  unfold PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop.body
  simp only [if_pos go,lift,bind_tc_ok,PV_RunJoin_CircleNeutralWide53.from32]
  change (do
    let x ← Array.index_usize rank at1
    let q ← (U64.wrapping_shl remainder 32#u32 ||| UScalar.cast .U64 x)/PV_RunJoin_SamplerDivWord54.prime
    let next ← Array.update rank at1 (UScalar.cast .U32 q)
    let rem ← (U64.wrapping_shl remainder 32#u32 ||| UScalar.cast .U64 x)%PV_RunJoin_SamplerDivWord54.prime
    ok (cont (next,rem,at1)))=ok _
  rw [hread,bind_tc_ok,hq,bind_tc_ok,hupdate,bind_tc_ok,hr,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_SamplerDivStep54
