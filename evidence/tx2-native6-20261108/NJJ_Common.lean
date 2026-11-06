import NJJ_QueryOps
import NJC_FilledClause
set_option autoImplicit false
noncomputable section
namespace NJJ_Common
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
abbrev Merkle := ∀ {H : Type}, aspis_core.digest.Digest32 H → Slice U8 → verifier.Prepared → Array U8 32#usize → Usize → H → Result (core.result.Result Unit verifier.Error)
abbrev Finish := verifier.View → verifier.Prepared → verifier.Accumulator → Option (verifier.Phase → Result Unit) → Result (core.result.Result Unit verifier.Error)

def resume (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8)
 (v : transport.Variant) (hash : H) :=
 NHT_ResultPort.action (NJC_ResumeCalls.reference (NJC_FilledClause.reserved reservation) d ck proof pub v hash)
def pending (reservation : NP6_StdModel.Reservation) :=
 Port3_NativePendingInstall.source (NJC_FilledClause.reserved reservation)
def query := NHT_PacketOps.query NJJ_QueryOps.concrete 0 0

/-- Dictionary-free source-model candidate. The two named sibling functions
are explicitly OPEN. The Reservation arguments are not yet attached to actual
allocator events and therefore FAIL (aq)(2)/(au)(5); no native root is claimed.
See NJJ_AllocatorSites.md. This body is a mechanical substitution in the pinned
NHT emitted common body, with all standard calls left literally in place. -/
def run (weightReservation rawReservation : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let r ←
    (resume weightReservation) aspis_coredigestDigest32Inst checkpoint proof public_bytes
      AspisR1Stage2.transport.Variant.S2 hash
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    if a.next != NHT_Constants.compact.SPLIT
    then ok (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint)
    else
      let g ← NHT_PacketOps.powers 29#usize p.gamma
      NHV_ReleaseOps.mark obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
      let i ← NHT_Constants.compact.OFF_INACTIVE
      let i1 ← NHT_Constants.compact.OFF_ROUND0
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i, «end» := i1 }
      let o ← NJC_ClosedCalls.inactive s
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
          merkle aspis_coredigestDigest32Inst proof p
            folded_root 1#usize hash
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          NHV_ReleaseOps.mark obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle NHT_Constants.compact.SPLIT)
          let r4 ← NJC_ClosedCalls.geometry p.queries a.next 22#usize
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← (pending rawReservation) s2
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                query proof p a g obs val2 val3
                  22#usize
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                let (a1, pending) := val4
                let (s3, deref_mut_back) ←
                  lift (alloc.vec.Vec.deref_mut a1.weights)
                let s4 ← Port3_FlushInstall.flush pending s3
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


def install (unused : VTop_Stages.Ops)
 (weightReservation rawReservation : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish) : VTop_Stages.Ops :=
 {unused with
 op18:=resume weightReservation,op17:=NHT_PacketOps.powers,op13:=NHV_ReleaseOps.mark,
 op2:=NJC_ClosedCalls.inactive,op5:=merkle,op11:=NJC_ClosedCalls.geometry,
 op10:=pending rawReservation,op6:=query,op9:=Port3_FlushInstall.flush,op19:=finish}

/-- Auxiliary mechanical specialization of the emitted body. `unused` is
absent from run; this is not a positive-root theorem under (aq)(2). -/
theorem source (unused : VTop_Stages.Ops)
 (weightReservation rawReservation : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NHT_EmittedCommon.tx2_common (install unused weightReservation rawReservation merkle finish) d pub proof ck hash none=
 run weightReservation rawReservation merkle finish d pub proof ck hash none := by rfl

#print axioms source
#print source
#print run
end NJJ_Common
