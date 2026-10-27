import RPu_FJa_FullLowWeight
import RPu_FJa_InternalLowWeight
import RPu_FJa_PreparedMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PoseidonLowOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (K Canon decode)
open FIv_PreparedNew (NP prepared)
open FJa_PoseidonOrigins (Openings Selectors)
/-- Derive the actual low weights and their prepared multipliers from the
SAME evaluator call. Leading/full/internal packed VALUES are still not claimed. -/
theorem value (o : Openings) (s : Selectors) (out : Array NQ 4#usize)
    (hc : FIw_ArrayValue.canonical s.local) (hb : Canon s.block)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
    ∃ (leadingLow fullLow internalLow : NQ) (weights : Array NP 3#usize) (block : NP),
      Canon leadingLow ∧ Canon fullLow ∧ Canon internalLow ∧
      decode leadingLow=FIv_NativeArray.value s.local 0 ∧
      decode fullLow=FIv_NativeArray.value s.local 1+FIv_NativeArray.value s.local 9+FIv_NativeArray.value s.local 10 ∧
      decode internalLow=FJa_LocalWeightFold.model s [2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize] 0 ∧
      FIq_Native.core.array.Array.map (BuiltinFnMut NQ NP)
        (Array.make 3#usize [leadingLow,fullLow,internalLow]) field.PreparedQm31Multiplier.new=ok weights ∧
      List.Forall₂ (fun x p=>ExtractedMaskPreparedState.PreparedFor (prepared p) (qm x))
        [leadingLow,fullLow,internalLow] weights.val ∧
      field.PreparedQm31Multiplier.new s.block=ok block ∧
      ExtractedMaskPreparedState.PreparedFor (prepared block) (qm s.block) := by
  obtain ⟨leadingLow,fullLow,internalLow,leading,full,internal,weights,block,h0,hf,hi,_,_,_,hw,hbcall,_⟩ :=
    FJa_PoseidonOrigins.reached o s out run
  have c0 := FIv_NativeArray.canonical s.local 0#usize leadingLow hc h0
  have v0 := FIv_NativeArray.read s.local 0#usize leadingLow h0
  have vf := FJa_FullLowWeight.value s fullLow hc hf
  have vi := FJa_InternalLowWeight.value s internalLow hc hi
  have cw : FIw_ArrayValue.canonical (Array.make 3#usize [leadingLow,fullLow,internalLow]) := by
    intro x hx
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact c0
    · exact vf.1
    · exact vi.1
  refine ⟨leadingLow,fullLow,internalLow,weights,block,c0,vf.1,vi.1,?_,vf.2,vi.2,hw,
    FJa_PreparedMap.value _ weights cw hw,hbcall,FIv_PreparedNew.valid s.block block hb hbcall⟩
  exact v0.symm
#print axioms value
end AspisR1.FJa_PoseidonLowOnRun
end
