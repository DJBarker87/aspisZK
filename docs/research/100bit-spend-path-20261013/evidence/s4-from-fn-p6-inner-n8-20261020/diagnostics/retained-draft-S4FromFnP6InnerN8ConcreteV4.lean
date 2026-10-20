import S4FromFnP6EightTraceV1
import S4FromFnP6FourTraceV1
import S4FromFnP6GeneratedTrace

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

/-- Successful generated inner callback execution exposes the exact source
array read and reducer call, and retains its closure array. -/
theorem innerCallback_success_parts
    (ops : FourDotsOps) (limbs : fast_dots.four_dots.closure.closure)
    (idx : Usize) {value : U32} {limbs' : fast_dots.four_dots.closure.closure}
    (h : fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      ops limbs idx = .ok (value, limbs')) :
    ∃ word, Array.index_usize limbs idx = .ok word ∧
      ops.m31ReduceU64 word = .ok value ∧ limbs' = limbs := by
  unfold fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut at h
  cases hi : Array.index_usize limbs idx with
  | fail e => simp only [hi, bind_tc_fail] at h; cases h
  | div => simp only [hi, bind_tc_div] at h; cases h
  | ok word =>
    cases hm : ops.m31ReduceU64 word with
    | fail e => simp only [hi, bind_tc_ok, hm, bind_tc_fail] at h; cases h
    | div => simp only [hi, bind_tc_ok, hm, bind_tc_div] at h; cases h
    | ok value' =>
      simp only [hi, bind_tc_ok, hm, bind_tc_ok] at h
      have hp := Result.ok.inj h
      rcases Prod.mk.inj hp with ⟨hv, hc⟩
      subst value'
      subst limbs'
      exact ⟨word, rfl, hm, rfl⟩

private theorem innerFnMutStep_at
    (ops : FourDotsOps) (limbs : fast_dots.four_dots.closure.closure)
    (n : Nat) (hn : n < 8) (hnval : (n#usize).val = n)
    (hnextval : ((n+1)#usize).val = n+1)
    {value : U32} {next : fast_dots.four_dots.closure.closure × Usize}
    (hstep : fnMutStep
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
      (limbs,n#usize) n = .ok (value,next)) :
    ∃ word, Array.index_usize limbs n#usize = .ok word ∧
      ops.m31ReduceU64 word = .ok value ∧
      next = (limbs,(n+1)#usize) := by
  have hpow8 : 8 < 2 ^ Usize.numBits := by
    rw [Usize.numBits]
    cases System.Platform.numBits_eq <;> norm_num
  have hmax : Usize.max + 1 = 2 ^ Usize.numBits := by
    rw [Usize.numBits]
    exact Usize.max_succ_eq_pow
  have hnplusBound : n + 1 ≤ Usize.max := by
    have hnplus : n + 1 < 2 ^ Usize.numBits := by omega
    omega
  obtain ⟨nextClosure,nextIndex,hcall,haddActual,hnext⟩ :=
    fnMutStep_success
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
      (limbs,n#usize) n hstep
  have hone : (1#usize).val = 1 := by scalar_tac
  have hbound : (n#usize).val + (1#usize).val ≤ Usize.max := by
    rw [hnval, hone]
    exact hnplusBound
  obtain ⟨boundedNext,hadd,hboundedVal⟩ :=
    WP.spec_imp_exists (Usize.add_spec (x := n#usize) (y := 1#usize) hbound)
  have hboundedVal' : boundedNext.val = n + 1 := by
    rw [hnval, hone] at hboundedVal
    exact hboundedVal
  have hboundedEq : boundedNext = (n+1)#usize := by
    apply UScalar.eq_of_val_eq
    rw [hboundedVal', hnextval]
  have hnextIndex : nextIndex = (n+1)#usize :=
    (Result.ok.inj (haddActual.symm.trans hadd)).trans hboundedEq
  have hcall' : fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      ops limbs n#usize = .ok (value,nextClosure) := by
    change fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      ops limbs n#usize = .ok (value,nextClosure)
    exact hcall
  obtain ⟨word,hindex,hreduce,hclosure⟩ :=
    innerCallback_success_parts ops limbs n#usize hcall'
  refine ⟨word,hindex,hreduce,?_⟩
  rw [hnext,hclosure,hnextIndex]



theorem innerArrayP6_success_values_match_fixedV6
    (ops : FourDotsOps)
    (limbs : fast_dots.four_dots.closure.closure)
    (values : Aeneas.Std.Array U32 8#usize)
    (h : arrayFromFnP6 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
      limbs = .ok values) :
    ∃ m0 m1 m2 m3 m4 m5 m6 m7 w0 w1 w2 w3 w4 w5 w6 w7,
      values.val = [m0,m1,m2,m3,m4,m5,m6,m7] ∧
      Array.index_usize limbs 0#usize = .ok w0 ∧ ops.m31ReduceU64 w0 = .ok m0 ∧
      Array.index_usize limbs 1#usize = .ok w1 ∧ ops.m31ReduceU64 w1 = .ok m1 ∧
      Array.index_usize limbs 2#usize = .ok w2 ∧ ops.m31ReduceU64 w2 = .ok m2 ∧
      Array.index_usize limbs 3#usize = .ok w3 ∧ ops.m31ReduceU64 w3 = .ok m3 ∧
      Array.index_usize limbs 4#usize = .ok w4 ∧ ops.m31ReduceU64 w4 = .ok m4 ∧
      Array.index_usize limbs 5#usize = .ok w5 ∧ ops.m31ReduceU64 w5 = .ok m5 ∧
      Array.index_usize limbs 6#usize = .ok w6 ∧ ops.m31ReduceU64 w6 = .ok m6 ∧
      Array.index_usize limbs 7#usize = .ok w7 ∧ ops.m31ReduceU64 w7 = .ok m7 := by
  have hN : (8#usize).val = 8 := by decide
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,s1,s2,s3,s4,s5,s6,s7,s8,
      hvalues,h0,h1,h2,h3,h4,h5,h6,h7⟩ :=
    arrayFromFnP6_success_eight_calls (8#usize) hN
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
      limbs h
  obtain ⟨w0,hi0,hm0,hs1⟩ := innerFnMutStep_at ops limbs 0 (by omega) (by rfl) (by rfl) h0
  rw [hs1] at h1
  obtain ⟨w1,hi1,hm1,hs2⟩ := innerFnMutStep_at ops limbs 1 (by omega) (by rfl) (by rfl) h1
  rw [hs2] at h2
  obtain ⟨w2,hi2,hm2,hs3⟩ := innerFnMutStep_at ops limbs 2 (by omega) (by rfl) (by rfl) h2
  rw [hs3] at h3
  obtain ⟨w3,hi3,hm3,hs4⟩ := innerFnMutStep_at ops limbs 3 (by omega) (by rfl) (by rfl) h3
  rw [hs4] at h4
  obtain ⟨w4,hi4,hm4,hs5⟩ := innerFnMutStep_at ops limbs 4 (by omega) (by rfl) (by rfl) h4
  rw [hs5] at h5
  obtain ⟨w5,hi5,hm5,hs6⟩ := innerFnMutStep_at ops limbs 5 (by omega) (by rfl) (by rfl) h5
  rw [hs6] at h6
  obtain ⟨w6,hi6,hm6,hs7⟩ := innerFnMutStep_at ops limbs 6 (by omega) (by rfl) (by rfl) h6
  rw [hs7] at h7
  obtain ⟨w7,hi7,hm7,_⟩ := innerFnMutStep_at ops limbs 7 (by omega) (by rfl) (by rfl) h7
  exact ⟨v0,v1,v2,v3,v4,v5,v6,v7,w0,w1,w2,w3,w4,w5,w6,w7,
    hvalues,hi0,hm0,hi1,hm1,hi2,hm2,hi3,hm3,hi4,hm4,hi5,hm5,hi6,hm6,hi7,hm7⟩

#print axioms innerCallback_success_parts
#print axioms innerArrayP6_success_values_match_fixedV6

end AspisR1FromFnP6Generated
