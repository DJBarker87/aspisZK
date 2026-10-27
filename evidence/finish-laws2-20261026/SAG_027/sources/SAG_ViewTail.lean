import Tx2I_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_ViewTail
open Aeneas Aeneas.Std Result VTop_Stages

def view (inactive : aspis_core.field.wide_exact.WideExact)
    (r0 r1 fm : Slice U8) : verifier.View :=
  {variant := .S2, semantic := Array.to_slice (Std.Array.empty U8),
   y1 := Array.to_slice (Std.Array.empty U8), inactive := inactive,
   round0 := r0, folded_root := none, round1 := r1, final_message := fm,
   query_bytes := Array.to_slice (Std.Array.empty U8)}

/-- Retain the exact source range results discarded by tail_reached. -/
theorem reached (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (obs : Option (verifier.Phase → Result Unit))
    (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
    (state : verifier.Accumulator × verifier.BatchedWeights)
    (accepted : Tx2I_Cuts.tail ops proof p obs inactive round0 folded round1 state = ok (.Ok ())) :
    ∃ (flushed : Slice aspis_core.field.QM31)
      (back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
      (r0 r1 fm : Slice U8) (finalStart queryStart : Usize),
      alloc.vec.Vec.deref_mut state.1.weights = (state.1.weights.deref,back) ∧
      ops.op9 state.2 state.1.weights.deref = ok flushed ∧
      ops.op21 = ok finalStart ∧ ops.op20 = ok queryStart ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start := round0, «end» := folded} = ok r0 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start := round1, «end» := finalStart} = ok r1 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start := finalStart, «end» := queryStart} = ok fm ∧
      ops.op19 (view inactive r0 r1 fm) p {state.1 with weights := back flushed} obs = ok (.Ok ()) := by
  unfold Tx2I_Cuts.tail at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals exact ⟨_,_,_,_,_,_,_,rfl,by assumption,by assumption,by assumption,
    by assumption,by assumption,by assumption,accepted⟩

#print axioms reached
end AspisR1.SAG_ViewTail
end
