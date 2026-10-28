import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1_QueryProducer
import PV_L1_Source_008
import PV_L1_Source_018
import PV_L1_Source_019
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_020
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts) :
  Logged (core.result.Result prover.Publication verifier.Error)
  := do
  let _ ← observe .opening 0 (ok ())
  let s := alloc.vec.Vec.deref prepared.folded_word
  let leaves ← PV_L1_Logged.lift (prover.folded_leaves hash s folded_salts)
  let o ← PV_L1_Logged.lift (host_tree.BinaryTree.new
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash leaves)
  let r ← PV_L1_Logged.lift (core.option.Option.ok_or o verifier.Error.Allocation)
  let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let root ← PV_L1_Logged.lift (host_tree.BinaryTree.root val)
    let s1 := alloc.vec.Vec.deref prepared.q1
    let s2 := alloc.vec.Vec.deref prepared.w1
    let c1 ← PV_L1_Logged.lift (prover.round s1 s2)
    let s3 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice c1))
    let c1bytes ← PV_L1_Logged.lift (prover.encoded_slice s3)
    let s4 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice root))
    let payload ← PV_L1_Logged.lift (alloc.slice.Slice.to_vec core.clone.CloneU8 s4)
    let s5 := alloc.vec.Vec.deref c1bytes
    let payload1 ← PV_L1_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 payload s5)
    let s6 := alloc.vec.Vec.deref payload1
    let (alpha1, transcript) ←
      PV_L1_Source_019.produce
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        prepared.transcript 30#u8 s6 false
    let s7 := alloc.vec.Vec.deref prepared.q1
    let final_message ← PV_L1_Logged.lift (prover.fold s7 alpha1 false)
    let s8 := alloc.vec.Vec.deref final_message
    let fbytes ← PV_L1_Logged.lift (prover.encoded_slice s8)
    let s9 := alloc.vec.Vec.deref fbytes
    let (r1, transcript1) ← PV_L1_Logged.lift (PV_L1_QueryProducer.produce
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript 31#u8 s9)
    let cf1 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s10 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8)))
      let _ ←
        PV_L1_Source_018.produce
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 32#u8 s10
      let scp ← PV_L1_Logged.lift (Array.index_usize prepared.sem.z 0#usize)
      let scp1 ← PV_L1_Logged.lift (Array.index_usize prepared.sem.z 1#usize)
      let s11 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice val1))
      let v ← PV_L1_Logged.lift (alloc.slice.Slice.to_vec core.clone.CloneU32 s11)
      let a ← PV_L1_Logged.lift (Array.index_usize prepared.sem.roots 0#usize)
      let r2 ←
        PV_L1_Source_008.produce variant
          {
            alpha := prepared.sem.alpha,
            z :=
              (Array.make 2#usize [
                Array.make 2#usize [ scp.x, scp.y ],
                Array.make 2#usize [ scp1.x, scp1.y ]
                ]),
            gamma := prepared.gamma,
            kappa := prepared.kappa,
            alpha0 := prepared.alpha0,
            alpha1,
            queries := v
          } a
      let cf2 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        Pure.pure (core.result.Result.Ok
          {
            backend := prepared.backend,
            semantic_bytes := prepared.sem.bytes,
            y1 := prepared.y1,
            inactive := prepared.inactive,
            c0bytes := prepared.c0bytes,
            root,
            c1bytes,
            fbytes,
            queries := val1,
            folded_word := prepared.folded_word,
            folded_salts,
            tree := val
          })
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.Publication (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.Publication (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      prover.Publication (core.convert.FromSame verifier.Error) residual

theorem complete_result
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts) :
  erase (produce variant hash prepared folded_salts) = prover.finish_opening variant hash prepared folded_salts := by
  unfold produce
  conv_rhs => unfold prover.finish_opening
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_QueryProducer.complete_result,PV_L1_Source_008.complete_result,PV_L1_Source_018.complete_result,PV_L1_Source_019.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_QueryProducer.complete_result,PV_L1_Source_008.complete_result,PV_L1_Source_018.complete_result,PV_L1_Source_019.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_QueryProducer.complete_result,PV_L1_Source_008.complete_result,PV_L1_Source_018.complete_result,PV_L1_Source_019.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_020
