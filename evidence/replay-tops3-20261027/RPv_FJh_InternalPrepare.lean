import RPv_FJh_InternalLaneLoop

/-! Derive the actual internal-linear prefix: nonzero-lane accumulator,
full-sum array, reconstructed zero lane and checked zero-lane update. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalPrepare
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.FJh_Base
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.FJh_InternalStateWords (wordVec wordVec_source wordVec_canonical)
open AspisR1.FJh_InternalAccumulatorModel (partSum wordVec_decode)
open AspisR1.FJh_InternalLaneReassembly (rawDecode zeroRun)
open AspisR1.FJh_InternalRawArrays (FullCallback)
open AspisR1.RawPoseidonRowField (decodeWords decodeWords_add)

def prepare (state : State) : Result (State × Raw4) := do
  let old ← Array.index_usize state 0#usize
  let part ← state_only_poseidon.internal_linear_lazy_loop0 state
    AspisR1.FJh_InternalAccumulateState.zero 1#usize
  let full ← array_from_fn_copy 4#usize core.marker.CopyU64 FullCallback 0#u64 (part,wordVec old)
  let value ← zeroRun part old
  let state1 ← Array.update state 0#usize value
  .ok (state1,full)

theorem wrapper_factor (state : State) :
    state_only_poseidon.internal_linear_lazy state = (do
      let (state1,full) ← prepare state
      state_only_poseidon.internal_linear_lazy_loop1
        { start := 1#usize, «end» := poseidon2.POSEIDON2_WIDTH } state1 full) := by
  simp only [state_only_poseidon.internal_linear_lazy,prepare,zeroRun,wordVec_source,
    AspisR1.FJh_InternalAccumulateState.zero,bind_assoc_eq,bind_tc_ok]
  all_goals rfl

theorem source_success (state : State) (hs : CanonicalState state) :
    ∃ state1 : State, ∃ full : Raw4, prepare state = .ok (state1,full) ∧
      CanonicalState state1 ∧ RawBound full (16*AspisV8R17.RawReducer.P) ∧
      rawDecode full = partSum state + Decode (cell state (0 : Fin 16)) ∧
      ∀ j : Fin 16, Decode (cell state1 j) =
        if j.val = 0 then partSum state - Decode (cell state (0 : Fin 16)) else Decode (cell state j) := by
  let old := cell state (0 : Fin 16)
  have hread : Array.index_usize state 0#usize = .ok old :=
    AspisR1.FJh_InternalStateWords.state_source_read state 0#usize (by decide)
  obtain ⟨part,hpart,hpartBound,hpartModel⟩ := AspisR1.FJh_InternalAccumulatorModel.source_success state hs
  change rawDecode part = partSum state at hpartModel
  have hwords := wordVec_canonical old (hs 0)
  obtain ⟨full,hfull,hfullBound,hfullValues⟩ :=
    AspisR1.FJh_InternalRawArrays.full_source part (wordVec old) hpartBound hwords
  have hpart16 : RawBound part (16*AspisV8R17.RawReducer.P) := by
    intro j
    have hb : 15*AspisV8R17.RawReducer.P < 16*AspisV8R17.RawReducer.P := by
      norm_num [AspisV8R17.RawReducer.P]
    exact Nat.lt_trans (hpartBound j) hb
  obtain ⟨value,hzero,hvalueCan,hvalueModel⟩ :=
    AspisR1.FJh_InternalLaneReassembly.zero_source part old hpart16 (hs 0)
  have hupdate : Array.update state 0#usize value = .ok (state.set 0#usize value) := by
    obtain ⟨out,hrun,hset⟩ := WP.spec_imp_exists (Array.update_spec state 0#usize value (by simp))
    simpa only [hset] using hrun
  have hfun : (fun j : Fin 4 => (cell full j).val) =
      (fun j => (cell part j).val + (cell (wordVec old) j).val) := funext hfullValues
  have hsum : rawDecode full = rawDecode part + Decode old :=
    (congrArg decodeWords hfun).trans
      ((decodeWords_add (fun j : Fin 4 => (cell part j).val)
        (fun j : Fin 4 => (cell (wordVec old) j).val)).trans
        (congrArg (rawDecode part + ·) (wordVec_decode old)))
  have hfullModel : rawDecode full = partSum state + Decode old :=
    hsum.trans (congrArg (· + Decode old) hpartModel)
  have hzeroModel : Decode value = partSum state - Decode old :=
    hvalueModel.trans (congrArg (· - Decode old) hpartModel)
  refine ⟨state.set 0#usize value,full,?_,set_canonical state 0#usize value hs hvalueCan,
    hfullBound,hfullModel,?_⟩
  · simp only [prepare,hread,hpart,hfull,hzero,hupdate,bind_tc_ok]
  · intro j
    rw [cell_set]
    have h0 : (0#usize).val = 0 := by decide
    rw [h0]
    by_cases hz : j.val = 0
    · rw [if_pos hz,if_pos hz]
      exact hzeroModel
    · rw [if_neg hz,if_neg hz]

#print axioms wrapper_factor
#print axioms source_success
end AspisR1.FJh_InternalPrepare
