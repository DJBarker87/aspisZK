import S1ClaimsSourceReadsV1
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisS1ClaimsUnrolledSource
/-- Four unresolved emitted primitives, as functions rather than axioms.
No concrete native instance or successful execution is asserted here. -/
structure PrimitivePorts where
  reserve : {T : Type} → (A : Type) → alloc.vec.Vec T → Std.Usize →
    Result ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T)
  intoBox : {T : Type} → (A : Type) → alloc.vec.Vec T → Result (Slice T)
  toArray : {T : Type} → (N : Std.Usize) → Slice T →
    Result (core.result.Result (Array T N) (Slice T))
  decode : (N : Std.Usize) → r1_wire.ValidatedRecord → Std.Usize →
    Result (core.result.Result (Array aspis_core.field.QM31 N) r1_wire.Error)

/-- [aspis_core::r0::heap::filled]:
    Source: '/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025/core-workspace/crates/aspis-core/src/r0/heap.rs', lines 5:0-5:67
    Name pattern: [aspis_core::r0::heap::filled]
    Visibility: public -/
@[rust_fun "aspis_core::r0::heap::filled"]
def aspis_core.r0.heap.filled
  {T : Type} (backend : PrimitivePorts) (coremarkerCopyInst : core.marker.Copy T) (n : Std.Usize)
  (value : T) :
  Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error)
  := do
  let (r, out) ←
    backend.reserve Global (alloc.vec.Vec.new T) n
  let r1 ←
    core.result.Result.map_err
      (aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
      coremarkerCopyInst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let out1 ← alloc.vec.Vec.resize coremarkerCopyInst.cloneInst out n value
    ok (core.result.Result.Ok out1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec T) (core.convert.FromSame aspis_core.r0.Error) residual

/-- [aspis_r1_cost_probe::candidate_claims::claims]:
    Source: 'src/candidate_claims.rs', lines 5:0-17:1 -/
def candidate_claims.claims
  (backend : PrimitivePorts) (prefix1 : r1_wire.Prefix) :
  Result (core.result.Result (Array (Array aspis_core.field.QM31 29#usize)
    3#usize) r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 25#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let a := Array.repeat 29#usize aspis_core.field.QM31.ZERO
    let r1 ←
      aspis_core.r0.heap.filled backend (Array.Insts.CoreMarkerCopy 29#usize
        aspis_core.field.QM31.Insts.CoreMarkerCopy) 3#usize a
    let r2 ←
      core.result.Result.map_err
        candidate_claims.claims.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s ← backend.intoBox Global val
      let r3 ←
        backend.toArray 3#usize s
      let r4 ←
        core.result.Result.map_err
          candidate_claims.claims.closure_1.Insts.CoreOpsFunctionFnOnceTupleBoxSliceArrayQM3129Error
          r3 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r5 ← backend.decode 29#usize vr 0#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let (_, index_mut_back) ← Array.index_mut_usize val1 0#usize
          let r6 ← backend.decode 29#usize vr 29#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let out := index_mut_back val2
            let (_, index_mut_back1) ← Array.index_mut_usize out 1#usize
            let r7 ← backend.decode 29#usize vr 58#usize
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let out1 := index_mut_back1 val3
              let out2 ← Array.update out1 2#usize val4
              ok (core.result.Result.Ok out2)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
                (core.convert.FromSame r1_wire.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
              (core.convert.FromSame r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
            (core.convert.FromSame r1_wire.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
          (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
        (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
      (core.convert.FromSame r1_wire.Error) residual

end AspisS1ClaimsUnrolledSource

#print axioms AspisS1ClaimsUnrolledSource.aspis_core.r0.heap.filled
#print axioms AspisS1ClaimsUnrolledSource.candidate_claims.claims
