import RPv_FJa_PoseidonOrigins
import RPv_FIv_NativeArray
import RPv_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_LocalWeightStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FJa_PoseidonOrigins (Selectors)
abbrev Call := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
/-- Original local-weight callback preserves its selector carrier and adds
precisely the selected cell, on the SAME accumulator/index. -/
theorem value (s last : Selectors) (acc out : NQ) (index : Usize)
    (hs : FIw_ArrayValue.canonical s.local) (hc : Canon acc)
    (run : Call s (acc,index)=ok (out,last)) :
    Canon out ∧ decode out=decode acc+FIv_NativeArray.value s.local index.val ∧ last=s := by
  unfold Call state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut at run
  obtain ⟨q,hq,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨sum,hsum,run⟩ := FIv_Map.bind_success _ _ _ run
  have same : (sum,s)=(out,last) := Result.ok.inj run
  cases same
  have v := FIv_NativeValue.add acc q out hc (FIv_NativeArray.canonical _ index q hs hq) hsum
  rw [←FIv_NativeArray.read _ index q hq] at v
  exact ⟨v.1,v.2,rfl⟩
/-- The internal callback is the SAME two source operations; only its closure
name differs. -/
theorem internal (s : Selectors) (acc : NQ) (index : Usize) :
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut s (acc,index)=Call s (acc,index) := rfl
#print axioms value
#print axioms internal
end AspisR1.FJa_LocalWeightStep
end
