import VTop_Model
set_option autoImplicit false
noncomputable section
namespace NHQ_Tx2CommonModel
open Aeneas Aeneas.Std Result VTop_Stages
abbrev R (A : Type) := core.result.Result A verifier.Error
variable {H : Type}
variable (ops : Ops) (digest : aspis_core.digest.Digest32 H)
variable (pub proof checkpoint : Slice U8) (hash : H)
variable (obs : Option (verifier.Phase → Result Unit))
/-- Retained emitted continuation. All runtime failures, divergence and errors remain. -/
def afterQuery (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (obs : Option (verifier.Phase → Result Unit)) (inactive : aspis_core.field.wide_exact.WideExact)
 (round0 folded round1 : Usize)
 (reply : R (verifier.Accumulator × verifier.BatchedWeights)) : Result (R Unit) := do
 let cf5 ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf5 with
 | core.ops.control_flow.ControlFlow.Continue val4 =>
   let (a1, pending) := val4
   let (s3, deref_mut_back) ←
     lift (alloc.vec.Vec.deref_mut a1.weights)
   let s4 ← ops.op9 pending s3
   let weights := deref_mut_back s4
   let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
   let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
   let s7 ←
     core.slice.index.Slice.index
       (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
       { start := round0, «end» := folded }
   let i5 ← ops.op21
   let s8 ←
     core.slice.index.Slice.index
       (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
       { start := round1, «end» := i5 }
   let i6 ← ops.op20
   let s9 ←
     core.slice.index.Slice.index
       (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
       { start := i5, «end» := i6 }
   let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
   ops.op19
     {
       variant := AspisR1Stage2.transport.Variant.S2,
       semantic := s5,
       y1 := s6,
       inactive := inactive,
       round0 := s7,
       folded_root := none,
       round1 := s8,
       final_message := s9,
       query_bytes := s10
     } p { a1 with weights } obs
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

def afterResume (r : R (verifier.Prepared × verifier.Accumulator)) : Result (R Unit) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    let i ← ops.op16
    if a.next != i
    then ok (core.result.Result.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint)
    else
      let g ← ops.op17 29#usize p.gamma
      ops.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
      let i1 ← ops.op23
      let i2 ← ops.op22
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i1, «end» := i2 }
      let o ← ops.op2 s
      let r1 ← ops.op0 o AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i3 ← ops.op15
        let i4 ← ops.op14
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
            { start := i3, «end» := i4 }
        let r2 ←
          core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
            s1
        let folded_root ←
          ops.unwrap32 r2
        let r3 ←
          ops.op5 digest proof p
            folded_root 1#usize hash
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ops.op13 obs (AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle i)
          let r4 ← ops.op11 p.queries a.next 22#usize
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← ops.op10 s2
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                ops.op6 proof p a g obs val2 val3
                  22#usize
              afterQuery ops proof p obs val1 i2 i3 i4 r6
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

def run : Result (R Unit) := do
 let r ← ops.op18 digest checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash
 afterResume ops digest proof hash obs r

theorem source : verifier.candidate.tx2_common ops digest pub proof checkpoint hash obs =
 run ops digest pub proof checkpoint hash obs := by rfl

theorem resume_reply (reply : R (verifier.Prepared × verifier.Accumulator))
 (resume_packet : ops.op18 digest checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash = ok reply) :
 run ops digest pub proof checkpoint hash obs = afterResume ops digest proof hash obs reply := by
 unfold run
 rw [resume_packet]
 rfl

theorem resume_error (error : verifier.Error)
 (resume_packet : ops.op18 digest checkpoint proof pub AspisR1Stage2.transport.Variant.S2 hash = ok (.Err error)) :
 run ops digest pub proof checkpoint hash obs = ok (.Err error) := by
 rw [resume_reply ops digest pub proof checkpoint hash obs (.Err error) resume_packet]
 rfl
theorem query_error (p : verifier.Prepared)
 (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
 (error : verifier.Error) :
 afterQuery ops proof p obs inactive round0 folded round1 (.Err error) = ok (.Err error) := by rfl

#print axioms query_error
#print axioms source
#print axioms resume_reply
#print axioms resume_error
end NHQ_Tx2CommonModel
