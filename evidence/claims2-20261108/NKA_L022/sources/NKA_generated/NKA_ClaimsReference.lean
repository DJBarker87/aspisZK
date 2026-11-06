import NKA_ClaimsModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_ClaimsReference
open Aeneas Aeneas.Std Result NJT_ClaimsRef

def reserveFilled {T : Type} (reservation : NP6_StdModel.Reservation)
 (copy : core.marker.Copy T) (n : Usize) (value : T) :
 Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error) :=
 match reservation with
 | .Ok _ => NJT_ClaimsRef.aspis_core.r0.heap.filled copy n value
 | .Err _ => ok (.Err .Allocation)

/-- Exact E001 emitted reference body, with the already-external heap.filled
reserve interpretation installed AT ITS ORIGINAL SITE. No changed Rust body,
new extraction or extended ReviewedTranscription item. Successful reservation
reduces to the original emitted body; rejection is the allocator outcome. -/
def run (reservation : NP6_StdModel.Reservation)
  (prefix1 : r1_wire.Prefix) :
  Result (core.result.Result (Slice (Array (Array aspis_core.field.QM31
    29#usize) 3#usize)) r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 25#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let r1 ← r1_wire.ValidatedRecord.decode_k 29#usize vr 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ← r1_wire.ValidatedRecord.decode_k 29#usize vr 29#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r3 ← r1_wire.ValidatedRecord.decode_k 29#usize vr 58#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r4 ←
            reserveFilled reservation (Array.Insts.CoreMarkerCopy 3#usize
              (Array.Insts.CoreMarkerCopy 29#usize
              aspis_core.field.QM31.Insts.CoreMarkerCopy)) 1#usize
              (Array.make 3#usize [ val, val1, val2 ])
          let r5 ←
            core.result.Result.map_err
              r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
              r4 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let s ← alloc.vec.Vec.into_boxed_slice Global val3
            ok (core.result.Result.Ok s)
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
              (core.convert.FromSame r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
            (core.convert.FromSame r1_wire.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
          (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
        (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
      (core.convert.FromSame r1_wire.Error) residual


theorem emitted_success (pre : r1_wire.Prefix) :
 run (.Ok ()) pre = NJT_ClaimsRef.r1_semantic.NJT_claims_ref pre := by rfl

#print axioms emitted_success
end AspisR1.NKA_ClaimsReference
end
