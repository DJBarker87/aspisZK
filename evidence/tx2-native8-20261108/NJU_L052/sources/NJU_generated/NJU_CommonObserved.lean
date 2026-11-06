import NJU_Log
set_option autoImplicit false
noncomputable section
namespace NJU_CommonObserved
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev K := aspis_core.field.QM31
abbrev R (A : Type) := Result (core.result.Result A verifier.Error)

/-- Actual child arguments and full observed Results at source call sites.
Std operations stay literal in the caller. Resume's internal observations
still require their own full native assembly; this log does not hide them. -/
inductive Event where
 | resume (ck proof pub : Slice U8) (reply : R (verifier.Prepared × verifier.Accumulator))
 | powers (gamma : E) (reply : Result (Array E 29#usize))
 | inactive (bytes : Slice U8) (reply : Result (Option E))
 | merkle (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) (reply : R Unit)
 | geometry (queries : Array U32 22#usize) (next : Usize) (reply : R verifier.QueryGeometry)
 | pending (weights : Slice K) (reply : R verifier.BatchedWeights)
 | query (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
   (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
   (reply : R (verifier.Accumulator × verifier.BatchedWeights))
 | flush (pending : verifier.BatchedWeights) (weights : Slice K) (reply : Result (Slice K))

abbrev Merkle := NJJ_Common.Merkle
abbrev Finish := NJJ_Common.Finish

def run (weightReservation rawReservation : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  NJU_Log.Run Event (core.result.Result Unit verifier.Error)
  := do
  let r ←
    NJU_Log.record (.resume checkpoint proof public_bytes)
      ((NJJ_Common.resume weightReservation) aspis_coredigestDigest32Inst checkpoint proof public_bytes
       AspisR1Stage2.transport.Variant.S2 hash)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    if a.next != NHT_Constants.compact.SPLIT
    then ok (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint)
    else
      let g ← NJU_Log.record (.powers p.gamma) (NHT_PacketOps.powers 29#usize p.gamma)
      NHV_ReleaseOps.mark obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
      let i ← NHT_Constants.compact.OFF_INACTIVE
      let i1 ← NHT_Constants.compact.OFF_ROUND0
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i, «end» := i1 }
      let o ← NJU_Log.record (.inactive s) (NJC_ClosedCalls.inactive s)
      let r1 ← NHT_Constants.core.option.Option.ok_or o AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i2 ← NHT_Constants.compact.OFF_FOLDED_ROOT
        let i3 ← NHT_Constants.compact.OFF_ROUND1
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
            { start := i2, «end» := i3 }
        let r2 ←
          core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
            s1
        let folded_root ←
          core.result.Result.unwrap core.fmt.DebugTryFromSliceError r2
        let r3 ←
          NJU_Log.record (.merkle proof p folded_root)
            (merkle aspis_coredigestDigest32Inst proof p folded_root 1#usize hash)
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          NHV_ReleaseOps.mark obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle NHT_Constants.compact.SPLIT)
          let r4 ← NJU_Log.record (.geometry p.queries a.next) (NJC_ClosedCalls.geometry p.queries a.next 22#usize)
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← NJU_Log.record (.pending s2) ((NJJ_Common.pending rawReservation) s2)
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                NJU_Log.record (.query proof p a g val2 val3)
                  (NJJ_Common.query proof p a g obs val2 val3 22#usize)
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                let (a1, pending) := val4
                let (s3, deref_mut_back) ←
                  lift (alloc.vec.Vec.deref_mut a1.weights)
                let s4 ← NJU_Log.record (.flush pending s3) (Port3_FlushInstall.flush pending s3)
                let weights := deref_mut_back s4
                let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s7 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i1, «end» := i2 }
                let i4 ← NHT_Constants.compact.OFF_FINAL
                let s8 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i3, «end» := i4 }
                let i5 ← NHT_Constants.compact.OFF_OPENINGS
                let s9 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i4, «end» := i5 }
                let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                finish
                  {
                    variant := AspisR1Stage2.transport.Variant.S2,
                    semantic := s5,
                    y1 := s6,
                    inactive := val1,
                    round0 := s7,
                    folded_root := none,
                    round1 := s8,
                    final_message := s9,
                    query_bytes := s10
                  } p { a1 with weights } obs
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame verifier.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame verifier.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual

/-- Forward erasure for ONE source invocation. This is a source observation
law, not the missing native G certificate. The callback parameters are
auxiliary and are forbidden as positive TX2:065 root hypotheses. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 (run wr rr merkle finish d pub proof ck hash none).result=
 NJJ_Common.run wr rr merkle finish d pub proof ck hash none := by
 simp only [run,NJJ_Common.run,NJU_Log.erase_bind,NJU_Log.erase_record,
  NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,
  NJU_Log.erase_flow,NJU_Log.prod_cases]
 apply NIL_ResultCases.bind_congr
 intro reply
 apply NIL_ResultCases.bind_congr
 intro flow
 cases flow with
 | Break residual => rfl
 | Continue pair =>
  rcases pair with ⟨prepared,accumulator⟩
  dsimp only
  simp only [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_liftM,NJU_Log.erase_if,
   NJU_Log.erase_flow,NJU_Log.prod_cases]
  repeat' first
  | intro
  | fail_if_no_progress dsimp only at *
  | rfl
  | (apply NIL_ResultCases.bind_congr; intro value
     cases value with
     | Continue payload => cases payload
     | Break residual => skip)
  | (apply NIL_ResultCases.bind_congr; intro value)
  | (fail_if_no_progress simp_all [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_liftM,
     NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,if_pos,if_neg])
  | split
  all_goals simp_all [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_liftM,
   NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases]

#print source
#print axioms source
end NJU_CommonObserved
