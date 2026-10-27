import R1Z.PV_RE_DictSuffix007
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix008
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.EncodingDomain.encode`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (self : host_commitment.EncodingDomain) (message : Array T 1024#usize) (out : Payload (alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new (alloc.vec.Vec
      T)) 4#usize)) : Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error) := do
  let (r, channels) := out
  let r1 ←
    core.result.Result.map_err
      (host_commitment.EncodingDomain.encode.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
      aspis_corer0scalarCodeFieldInst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let r2 ←
      host_commitment.EncodingDomain.encode_channel
        aspis_corer0scalarCodeFieldInst self message 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let channels1 ← alloc.vec.Vec.push channels val
      let r3 ←
        host_commitment.EncodingDomain.encode_channel
          aspis_corer0scalarCodeFieldInst self message 1#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let channels2 ← alloc.vec.Vec.push channels1 val1
        let r4 ←
          host_commitment.EncodingDomain.encode_channel
            aspis_corer0scalarCodeFieldInst self message 2#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let channels3 ← alloc.vec.Vec.push channels2 val2
          let r5 ←
            host_commitment.EncodingDomain.encode_channel
              aspis_corer0scalarCodeFieldInst self message 3#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let channels4 ← alloc.vec.Vec.push channels3 val3
            let i ← aspis_core.r0.WORD_LEN
            let t ← aspis_corer0scalarCodeFieldInst.ZERO
            let r6 ←
              aspis_core.r0.heap.filled
                aspis_corer0scalarCodeFieldInst.coremarkerCopyInst i t
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let count := alloc.vec.Vec.len self.xy
              let word ←
                host_commitment.EncodingDomain.encode_loop
                  aspis_corer0scalarCodeFieldInst self.xy channels4 val4 count
                  0#usize
              ok (core.result.Result.Ok word)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec T) (core.convert.FromSame aspis_core.r0.Error)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec T) (core.convert.FromSame aspis_core.r0.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec T) (core.convert.FromSame aspis_core.r0.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec T) (core.convert.FromSame aspis_core.r0.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec T) (core.convert.FromSame aspis_core.r0.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec T) (core.convert.FromSame aspis_core.r0.Error) residual


end R1Z.PV_RE_DictSuffix008
pv_dict_congr ProverRwFull.host_commitment.EncodingDomain.encode
pv_dict_congr R1Z.PV_RE_DictSuffix008.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_commitment.EncodingDomain.encode
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix008.continueAfter
