import Port3_NativeFinishBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGM_FinishControl
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeFinishBody
abbrev R (A : Type) := core.result.Result A verifier.Error
abbrev E := aspis_core.field.wide_exact.WideExact
variable {W A B : Type}
def bindChild (action : Result (R A)) (next : A → Result (R B)) : Result (R B) := do
 let reply ← action
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | core.ops.control_flow.ControlFlow.Continue value => next value
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    B (core.convert.FromSame verifier.Error) residual

theorem branch_normal (reply : R A) (next : A → Result (R B)) :
 (do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
  match cf with
  | core.ops.control_flow.ControlFlow.Continue value => next value
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     B (core.convert.FromSame verifier.Error) residual) =
 (match reply with | .Ok value=>next value | .Err error=>ok (.Err error)) := by
 cases reply <;> rfl

/-- Both Query rejections, including short-circuit on the counter, remain. -/
def afterDot (ops : Ops W) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (actual : E) : Result (R Unit) := do
 ops.op0 17#u16 0#usize actual
 ops.op0 17#u16 1#usize a.rhs
 if a.next != 22#usize then ok (.Err .Query)
 else
  let different ← ops.ne actual a.rhs
  if different then ok (.Err .Query)
  else
   ops.op1 obs .Final
   ok (.Ok ())

def afterPair (ops : Ops W) (v : verifier.View) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (claim pair : E) : Result (R Unit) := do
 ops.op0 16#u16 0#usize pair
 ops.op0 16#u16 1#usize claim
 let different ← ops.ne pair claim
 if different then ok (.Err .Relation)
 else
  ops.op1 obs .Relation
  bindChild (ops.op4 v.final_message a.weights.deref) (afterDot ops a obs)

def afterClaim (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (folds : Usize) (claim : E) : Result (R Unit) :=
 bindChild (ops.op3 p.variant p.semantic_alpha p.z) fun weights => do
 let alpha ← core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=folds}
 bindChild (ops.op2 weights alpha v.final_message p.kappa) (afterPair ops v a obs claim)

def run (ops : Ops W)
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


/-- Complete source Result normal form, preserving child errors, runtime
failure/divergence, stateful callback order and every rejection branch. -/
theorem source (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
 Port3_NativeFinishBody.verifier.finish_relation ops v p a obs = run ops v p a obs := by
 rfl
#print axioms branch_normal
#print axioms source
end AspisR1.NGM_FinishControl
end
