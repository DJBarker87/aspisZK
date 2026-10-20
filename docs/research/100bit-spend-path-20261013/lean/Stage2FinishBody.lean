import Stage2ContinuationTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
namespace Stage2Finish
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev K := aspis_core.field.QM31
abbrev M := aspis_core.field.M31
/-- Typed backend frontiers of the emitted finish, not correctness axioms. -/
structure FinishOps (W : Type) where
  field : Slice U8 → Usize → Result E
  quarter : Result M
  add : E → E → Result E
  mulM : E → M → Result E
  ne : E → E → Result Bool
  polynomial : Slice U8 → E → Result E
  trace : U16 → Usize → E → Result Unit
  folds : transport.Variant → Result Usize
  newWeights : transport.Variant → Array K 10#usize → Array aspis_core.circle.SecureCirclePoint 2#usize → Result (core.result.Result W verifier.Error)
  pair : W → Slice E → Slice U8 → E → Result (core.result.Result E verifier.Error)
  mark : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit
  dot : Slice U8 → Slice K → Result (core.result.Result E verifier.Error)
variable {W : Type}
def verifier.finishRelationRoundWithOps (ops : FinishOps W)
  (poly : Slice Std.U8) (alpha : aspis_core.field.wide_exact.WideExact)
  (claim : aspis_core.field.wide_exact.WideExact) (round : Std.Usize) :
  Result (core.result.Result aspis_core.field.wide_exact.WideExact
    verifier.Error)
  := do
  let we ← ops.field poly 0#usize
  let we1 ← ops.field poly 4#usize
  let lhs ← ops.add we we1
  let m ← ops.quarter
  let rhs ← ops.mulM claim m
  let i ← 3#usize * round
  ops.trace 15#u16 i lhs
  let i1 ← i + 1#usize
  ops.trace 15#u16 i1 rhs
  let b ←
    ops.ne lhs
      rhs
  if b
  then ok (core.result.Result.Err verifier.Error.Relation)
  else
    let claim1 ← ops.polynomial poly alpha
    let i2 ← i + 2#usize
    ops.trace 15#u16 i2 claim1
    ok (core.result.Result.Ok claim1)

def verifier.finishRelationWithOps (ops : FinishOps W)
  (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let we ← Array.index_usize p.alpha 0#usize
  let r ← verifier.finishRelationRoundWithOps ops v.round0 we p.claim 0#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i ← ops.folds p.variant
    if i = 2#usize
    then
      let we1 ← Array.index_usize p.alpha 1#usize
      let r1 ← verifier.finishRelationRoundWithOps ops v.round1 we1 val 1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← ops.newWeights p.variant p.semantic_alpha p.z
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let s ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice
              aspis_core.field.wide_exact.WideExact)) p.alpha { «end» := i }
          let r3 ← ops.pair val2 s v.final_message p.kappa
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            ops.trace 16#u16 0#usize val3
            ops.trace 16#u16 1#usize val1
            let b ←
              ops.ne
                val3 val1
            if b
            then ok (core.result.Result.Err verifier.Error.Relation)
            else
              ops.mark obs verifier.Phase.Relation
              let s1 := alloc.vec.Vec.deref a.weights
              let r4 ← ops.dot v.final_message s1
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                ops.trace 17#u16 0#usize val4
                ops.trace 17#u16 1#usize a.rhs
                if a.next != 22#usize
                then ok (core.result.Result.Err verifier.Error.Query)
                else
                  let b1 ←
                    ops.ne
                      val4 a.rhs
                  if b1
                  then ok (core.result.Result.Err verifier.Error.Query)
                  else
                    ops.mark obs verifier.Phase.Final
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
      let r1 ← ops.newWeights p.variant p.semantic_alpha p.z
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice
            aspis_core.field.wide_exact.WideExact)) p.alpha { «end» := i }
        let r2 ← ops.pair val1 s v.final_message p.kappa
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ops.trace 16#u16 0#usize val2
          ops.trace 16#u16 1#usize val
          let b ←
            ops.ne
              val2 val
          if b
          then ok (core.result.Result.Err verifier.Error.Relation)
          else
            ops.mark obs verifier.Phase.Relation
            let s1 := alloc.vec.Vec.deref a.weights
            let r3 ← ops.dot v.final_message s1
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              ops.trace 17#u16 0#usize val3
              ops.trace 17#u16 1#usize a.rhs
              if a.next != 22#usize
              then ok (core.result.Result.Err verifier.Error.Query)
              else
                let b1 ←
                  ops.ne
                    val3 a.rhs
                if b1
                then ok (core.result.Result.Err verifier.Error.Query)
                else
                  ops.mark obs verifier.Phase.Final
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


end Stage2Finish
end AspisR1Stage2
