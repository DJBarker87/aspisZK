import T2Nat_Silent
import Port4D_FinishInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_FinishCode
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_Silent
variable {W : Type}

/-- Reification of the emitted parent, in the same source branch order.
Every primitive has its full Result; no success or comparison is assumed. -/
def parent (ops : Port3_NativeFinishBody.Ops W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit)) :
    Silent (core.result.Result Unit verifier.Error) := do
  let we ← call (Array.index_usize p.alpha 0#usize)
  let r ← call (ops.op5 v.round0 we p.claim 0#usize)
  let cf ← call (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i ← call (ops.op6 p.variant)
    if i = 2#usize
    then
      let we1 ← call (Array.index_usize p.alpha 1#usize)
      let r1 ← call (ops.op5 v.round1 we1 val 1#usize)
      let cf1 ← call (core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← call (ops.op3 p.variant p.semantic_alpha p.z)
        let cf2 ← call (core.result.Result.Insts.CoreOpsTry.branch r2)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let s ← call (core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice
              aspis_core.field.wide_exact.WideExact)) p.alpha { «end» := i })
          let r3 ← call (ops.op2 val2 s v.final_message p.kappa)
          let cf3 ← call (core.result.Result.Insts.CoreOpsTry.branch r3)
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            call (ops.op0 16#u16 0#usize val3)
            call (ops.op0 16#u16 1#usize val1)
            let b ← call (ops.ne
                val3 val1)
            if b
            then pure (core.result.Result.Err verifier.Error.Relation)
            else
              call (ops.op1 obs verifier.Phase.Relation)
              let s1 := alloc.vec.Vec.deref a.weights
              let r4 ← call (ops.op4 v.final_message s1)
              let cf4 ← call (core.result.Result.Insts.CoreOpsTry.branch r4)
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                call (ops.op0 17#u16 0#usize val4)
                call (ops.op0 17#u16 1#usize a.rhs)
                if a.next != 22#usize
                then pure (core.result.Result.Err verifier.Error.Query)
                else
                  let b1 ← call (ops.ne
                      val4 a.rhs)
                  if b1
                  then pure (core.result.Result.Err verifier.Error.Query)
                  else
                    call (ops.op1 obs verifier.Phase.Final)
                    pure (core.result.Result.Ok ())
              | core.ops.control_flow.ControlFlow.Break residual =>
                call (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame verifier.Error) residual)
          | core.ops.control_flow.ControlFlow.Break residual =>
            call (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame verifier.Error) residual)
        | core.ops.control_flow.ControlFlow.Break residual =>
          call (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame verifier.Error) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        call (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual)
    else
      let r1 ← call (ops.op3 p.variant p.semantic_alpha p.z)
      let cf1 ← call (core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s ← call (core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice
            aspis_core.field.wide_exact.WideExact)) p.alpha { «end» := i })
        let r2 ← call (ops.op2 val1 s v.final_message p.kappa)
        let cf2 ← call (core.result.Result.Insts.CoreOpsTry.branch r2)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          call (ops.op0 16#u16 0#usize val2)
          call (ops.op0 16#u16 1#usize val)
          let b ← call (ops.ne
              val2 val)
          if b
          then pure (core.result.Result.Err verifier.Error.Relation)
          else
            call (ops.op1 obs verifier.Phase.Relation)
            let s1 := alloc.vec.Vec.deref a.weights
            let r3 ← call (ops.op4 v.final_message s1)
            let cf3 ← call (core.result.Result.Insts.CoreOpsTry.branch r3)
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              call (ops.op0 17#u16 0#usize val3)
              call (ops.op0 17#u16 1#usize a.rhs)
              if a.next != 22#usize
              then pure (core.result.Result.Err verifier.Error.Query)
              else
                let b1 ← call (ops.ne
                    val3 a.rhs)
                if b1
                then pure (core.result.Result.Err verifier.Error.Query)
                else
                  call (ops.op1 obs verifier.Phase.Final)
                  pure (core.result.Result.Ok ())
            | core.ops.control_flow.ControlFlow.Break residual =>
              call (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame verifier.Error) residual)
        | core.ops.control_flow.ControlFlow.Break residual =>
          call (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame verifier.Error) residual)
      | core.ops.control_flow.ControlFlow.Break residual =>
        call (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual)
  | core.ops.control_flow.ControlFlow.Break residual =>
    call (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual)

theorem parent_erase (ops : Port3_NativeFinishBody.Ops W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit)) :
    erase (parent ops v p a obs) =
      Port3_NativeFinishBody.verifier.finish_relation ops v p a obs := by
  simp only [parent,Port3_NativeFinishBody.verifier.finish_relation,
    erase_bind,erase_call,erase_pure]

/-- Full Result and ordered log, for every error/failure branch as well as
success; the initial history is arbitrary and preserved byte for byte. -/
theorem parent_effects {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (ops : Port3_NativeFinishBody.Ops W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
    (before : CheckpointBytes5Effect.Log) :
    CheckpointBytes5Effect.run D hash (code (parent ops v p a obs)) before =
      (do let result ← Port3_NativeFinishBody.verifier.finish_relation ops v p a obs
          ok (result,before)) := by
  rw [ordered_log,parent_erase]

#print axioms parent_erase
#print axioms parent_effects
end AspisR1.T2Nat_FinishCode
end
