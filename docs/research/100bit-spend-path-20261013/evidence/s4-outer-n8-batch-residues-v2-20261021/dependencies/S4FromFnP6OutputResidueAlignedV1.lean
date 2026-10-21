import AspisR1FastDotsCurrentM31OpsBinding
import S4FromFnP6OutputBoundAlignedV1
import S4FromFnP6InnerN8ActualResidueV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false
namespace AspisR1FromFnP6Generated

private theorem reducer_success_actual
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (hbinding : ∀ x, ops.m31ReduceU64 x =
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x)
    (x : Std.U64) (z : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (h : ops.m31ReduceU64 x = .ok z) :
    z.val = x.val % AspisV8R17.RawReducer.P ∧ z.val < AspisV8R17.RawReducer.P := by
  have hcurrent :
      (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer ops).m31ReduceU64 x = .ok z := by
    rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding, ← hbinding x]
    exact h
  exact AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod ops x z hcurrent

private theorem composedN8_array_success_actual_residues
    (ops : FourDotsOps)
    (limbs : Aeneas.Std.Array Std.U64 8#usize)
    (vals : Aeneas.Std.Array Std.U32 8#usize)
    (harray : (fourDotsOpsWithP6ArrayFromFnN4N8
      (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN4N8
          (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs = .ok vals) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7,
      Array.index_usize limbs 0#usize = .ok w0 ∧
      Array.index_usize limbs 1#usize = .ok w1 ∧
      Array.index_usize limbs 2#usize = .ok w2 ∧
      Array.index_usize limbs 3#usize = .ok w3 ∧
      Array.index_usize limbs 4#usize = .ok w4 ∧
      Array.index_usize limbs 5#usize = .ok w5 ∧
      Array.index_usize limbs 6#usize = .ok w6 ∧
      Array.index_usize limbs 7#usize = .ok w7 ∧
      vals.val.map (fun word => word.val) =
        [w0.val % AspisV8R17.RawReducer.P, w1.val % AspisV8R17.RawReducer.P,
         w2.val % AspisV8R17.RawReducer.P, w3.val % AspisV8R17.RawReducer.P,
         w4.val % AspisV8R17.RawReducer.P, w5.val % AspisV8R17.RawReducer.P,
         w6.val % AspisV8R17.RawReducer.P, w7.val % AspisV8R17.RawReducer.P] ∧
      (∀ value ∈ vals.val, value.val < AspisV8R17.RawReducer.P) := by
  let actualOps := AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops
  let callbackOuter :=
    fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
      (fourDotsOpsWithP6ArrayFromFnN4N8 actualOps)
  let callbackInner :=
    fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
      (fourDotsOpsWithP6ArrayFromFnN8 actualOps)
  have hcallback : callbackOuter = callbackInner := rfl
  have hcallbackArray : arrayFromFnP6 8#usize callbackOuter limbs =
      arrayFromFnP6 8#usize callbackInner limbs :=
    congrArg (fun cb => arrayFromFnP6 8#usize cb limbs) hcallback
  have houter : arrayFromFnP6 8#usize callbackOuter limbs = .ok vals := by
    change (if (8#usize).val = 4 then arrayFromFnP6 8#usize callbackOuter limbs
      else if (8#usize).val = 8 then arrayFromFnP6 8#usize callbackOuter limbs
      else actualOps.arrayFromFn 8#usize callbackOuter limbs) = .ok vals at harray
    simpa only [if_neg (by decide : (8#usize).val ≠ 4),
      if_pos (by decide : (8#usize).val = 8)] using harray
  have hinnerP6 : arrayFromFnP6 8#usize callbackInner limbs = .ok vals :=
    hcallbackArray.symm.trans houter
  have hmodel : (fourDotsOpsWithP6ArrayFromFnN8 actualOps).arrayFromFn 8#usize
      callbackInner limbs = .ok vals := by
    simpa only [fourDotsOpsWithP6ArrayFromFnN8,
      if_pos (by decide : (8#usize).val = 8)] using hinnerP6
  obtain ⟨m0,m1,m2,m3,m4,m5,m6,m7,w0,w1,w2,w3,w4,w5,w6,w7,
      hvalues,hi0,hr0,hi1,hr1,hi2,hr2,hi3,hr3,
      hi4,hr4,hi5,hr5,hi6,hr6,hi7,hr7⟩ :=
    generatedInnerN8ArrayField_success_values_match_fixedV6 actualOps limbs vals hmodel
  have hbinding : ∀ x, actualOps.m31ReduceU64 x =
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := by
    intro x
    rfl
  have ⟨hm0,hc0⟩ := reducer_success_actual actualOps hbinding w0 m0 hr0
  have ⟨hm1,hc1⟩ := reducer_success_actual actualOps hbinding w1 m1 hr1
  have ⟨hm2,hc2⟩ := reducer_success_actual actualOps hbinding w2 m2 hr2
  have ⟨hm3,hc3⟩ := reducer_success_actual actualOps hbinding w3 m3 hr3
  have ⟨hm4,hc4⟩ := reducer_success_actual actualOps hbinding w4 m4 hr4
  have ⟨hm5,hc5⟩ := reducer_success_actual actualOps hbinding w5 m5 hr5
  have ⟨hm6,hc6⟩ := reducer_success_actual actualOps hbinding w6 m6 hr6
  have ⟨hm7,hc7⟩ := reducer_success_actual actualOps hbinding w7 m7 hr7
  refine ⟨w0,w1,w2,w3,w4,w5,w6,w7,hi0,hi1,hi2,hi3,hi4,hi5,hi6,hi7,?_,?_⟩
  · simp only [hvalues,List.map_cons,List.map_nil,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7]
  · intro value hv
    rw [hvalues] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

#print axioms composedN8_array_success_actual_residues

#print axioms composedN8_array_success_actual_residues
end AspisR1FromFnP6Generated
