import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_003
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_007
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (variant : transport.Variant) (p : prover.Publication) :
  Logged (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  let _ ← observe .publication 0 (ok ())
  let i ← PV_L1D_Logged.lift (compact.PROOF_BYTES)
  let out := alloc.vec.Vec.with_capacity Std.U8 i
  let a ← PV_L1D_Logged.lift (compact.MAGIC)
  let s ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice a))
  let out1 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s)
  let i1 ← PV_L1D_Logged.lift (transport.Variant.tag variant)
  let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice
      (Array.make 8#usize [ i1, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8 ])))
  let out2 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s1)
  let s2 := alloc.vec.Vec.deref p.semantic_bytes
  let (r, out3) ← PV_L1D_Logged.lift (host_compact.compact_semantic s2 out2)
  let r1 ← PV_L1D_Logged.lift (core.result.Result.map_err
      prover.publish_compact.closure.Insts.CoreOpsFunctionFnOnceTupleCodecErrorError
      r ())
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let s3 := alloc.vec.Vec.deref p.y1
    let (r2, out4) ← PV_L1D_Logged.lift (host_compact.compact_values s3 out3)
    let r3 ← PV_L1D_Logged.lift (core.result.Result.map_err
        prover.publish_compact.closure_1.Insts.CoreOpsFunctionFnOnceTupleCodecErrorError
        r2 ())
    let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a1 ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive)
      let s4 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice a1))
      let out5 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out4 s4)
      let s5 := alloc.vec.Vec.deref p.c0bytes
      let out6 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out5 s5)
      let s6 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice p.root))
      let out7 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out6 s6)
      let s7 := alloc.vec.Vec.deref p.c1bytes
      let out8 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out7 s7)
      let s8 := alloc.vec.Vec.deref p.fbytes
      let out9 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out8 s8)
      let left_val := alloc.vec.Vec.len out9
      let right_val ← PV_L1D_Logged.lift (compact.OFF_OPENINGS)
      massert (left_val = right_val)
      let (o, _) := core.option.Option.take p.backend.c1
      let cc1 ← PV_L1D_Logged.lift (core.option.Option.unwrap o)
      let (o1, _) := core.option.Option.take p.backend.c2
      let cc2 ← PV_L1D_Logged.lift (core.option.Option.unwrap o1)
      let s9 := alloc.vec.Vec.deref p.folded_word
      let out10 ←
        PV_L1D_Source_003.produce out9 cc1 cc2 p.queries s9 p.folded_salts
      let left_val1 := alloc.vec.Vec.len out10
      let right_val1 ← PV_L1D_Logged.lift (compact.OFF_NODES)
      massert (left_val1 = right_val1)
      let r4 ← PV_L1D_Logged.lift (prover.append_node_slots out10 cc1 cc2 p.tree p.queries)
      let cf2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r4)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let left_val2 := alloc.vec.Vec.len val
        massert (left_val2 = i)
        Pure.pure (core.result.Result.Ok val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

theorem complete_result
  (variant : transport.Variant) (p : prover.Publication) :
  erase (produce variant p) = prover.publish_compact variant p := by
  unfold produce
  conv_rhs => unfold prover.publish_compact
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_003.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_003.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_003.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_007
