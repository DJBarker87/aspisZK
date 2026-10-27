import FJa_PoseidonOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalPairOrigins
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
abbrev State := Array NQ 16#usize
/-- Actual selector interpolation and round cuts of one native pair call. -/
theorem reached (s l out : State)
    (run : state_only_poseidon.interpolated_internal_pair s l=ok out) :
    ∃ (w : Array NQ 7#usize) (e o : Array U32 7#usize) (even odd : NQ) (mid : State),
      FIq_Native.core.array.Array.map
        state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        state_only_poseidon.interpolated_internal_pair.ROWS l=ok w ∧
      FIq_Native.core.array.Array.map
        state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
        state_only_poseidon.interpolated_internal_pair.ROWS ()=ok e ∧
      FIq_Native.core.array.Array.map
        state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
        state_only_poseidon.interpolated_internal_pair.ROWS ()=ok o ∧
      field.qm31_m31_dot (Array.to_slice w) (Array.to_slice e)=ok even ∧
      field.qm31_m31_dot (Array.to_slice w) (Array.to_slice o)=ok odd ∧
      state_only_poseidon.internal_round s even=ok mid ∧
      state_only_poseidon.internal_round mid odd=ok out := by
  unfold state_only_poseidon.interpolated_internal_pair at run
  obtain ⟨w,rw,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨e,re,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨o,ro,run⟩ := FIv_Map.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨even,reven,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨odd,rodd,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨mid,rm,run⟩ := FIv_Map.bind_success _ _ _ run
  exact ⟨w,e,o,even,odd,mid,rw,re,ro,reven,rodd,rm,run⟩
#print axioms reached
end AspisR1.FJh_InternalPairOrigins
end
