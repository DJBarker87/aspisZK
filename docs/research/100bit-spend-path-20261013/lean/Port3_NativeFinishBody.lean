import Port3_NativePendingPrefix
import Stage2FinishBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeFinishBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
variable {W : Type}
structure Ops (W : Type) where
  op0 : Std.U16 → Std.Usize → aspis_core.field.wide_exact.WideExact → Result
        Unit
  op1 : (Option (verifier.Phase → Result Unit)) → verifier.Phase → Result Unit
  op2 : W → (Slice aspis_core.field.wide_exact.WideExact) → (Slice
        Std.U8) → aspis_core.field.wide_exact.WideExact → Result
        (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error)
  op3 : transport.Variant → (Array aspis_core.field.QM31 10#usize) → (Array
        aspis_core.circle.SecureCirclePoint 2#usize) → Result (core.result.Result
        W verifier.Error)
  op4 : (Slice Std.U8) → (Slice aspis_core.field.QM31) → Result
        (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error)
  op5 : (Slice Std.U8) → aspis_core.field.wide_exact.WideExact →
        aspis_core.field.wide_exact.WideExact → Std.Usize → Result
        (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error)
  op6 : transport.Variant → Result Std.Usize
  ne : aspis_core.field.wide_exact.WideExact → aspis_core.field.wide_exact.WideExact → Result Bool

def verifier.finish_relation (ops : Ops W)
  (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let we ← Array.index_usize p.alpha 0#usize
  let r ← ops.op5 v.round0 we p.claim 0#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i ← ops.op6 p.variant
    if i = 2#usize
    then
      let we1 ← Array.index_usize p.alpha 1#usize
      let r1 ← ops.op5 v.round1 we1 val 1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← ops.op3 p.variant p.semantic_alpha p.z
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let s ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice
              aspis_core.field.wide_exact.WideExact)) p.alpha { «end» := i }
          let r3 ← ops.op2 val2 s v.final_message p.kappa
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            ops.op0 16#u16 0#usize val3
            ops.op0 16#u16 1#usize val1
            let b ←
              ops.ne
                val3 val1
            if b
            then ok (core.result.Result.Err verifier.Error.Relation)
            else
              ops.op1 obs verifier.Phase.Relation
              let s1 := alloc.vec.Vec.deref a.weights
              let r4 ← ops.op4 v.final_message s1
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                ops.op0 17#u16 0#usize val4
                ops.op0 17#u16 1#usize a.rhs
                if a.next != 22#usize
                then ok (core.result.Result.Err verifier.Error.Query)
                else
                  let b1 ←
                    ops.ne
                      val4 a.rhs
                  if b1
                  then ok (core.result.Result.Err verifier.Error.Query)
                  else
                    ops.op1 obs verifier.Phase.Final
                    ok (core.result.Result.Ok ())
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
    else
      let r1 ← ops.op3 p.variant p.semantic_alpha p.z
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice
            aspis_core.field.wide_exact.WideExact)) p.alpha { «end» := i }
        let r2 ← ops.op2 val1 s v.final_message p.kappa
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ops.op0 16#u16 0#usize val2
          ops.op0 16#u16 1#usize val
          let b ←
            ops.ne
              val2 val
          if b
          then ok (core.result.Result.Err verifier.Error.Relation)
          else
            ops.op1 obs verifier.Phase.Relation
            let s1 := alloc.vec.Vec.deref a.weights
            let r3 ← ops.op4 v.final_message s1
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              ops.op0 17#u16 0#usize val3
              ops.op0 17#u16 1#usize a.rhs
              if a.next != 22#usize
              then ok (core.result.Result.Err verifier.Error.Query)
              else
                let b1 ←
                  ops.ne
                    val3 a.rhs
                if b1
                then ok (core.result.Result.Err verifier.Error.Query)
                else
                  ops.op1 obs verifier.Phase.Final
                  ok (core.result.Result.Ok ())
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


#print axioms verifier.finish_relation
end AspisR1.Port3_NativeFinishBody
end
