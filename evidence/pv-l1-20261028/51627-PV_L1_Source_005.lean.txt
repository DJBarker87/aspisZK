import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_005
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize) (batch : Std.Usize) (t : Std.Usize) :
  Logged (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  let _ ← observe .publication 0 (ok ())
  let begin1 ← PV_L1_Logged.lift (if batch = 0#usize
                 then Pure.pure 0#usize
                 else Pure.pure compact.SPLIT)
  let end1 ← PV_L1_Logged.lift (if batch = 0#usize
               then Pure.pure compact.SPLIT
               else Pure.pure 22#usize)
  let idx ← PV_L1_Logged.lift (prover.publication_indices queries begin1 end1 (t = 2#usize))
  let o ← PV_L1_Logged.lift (match t.val with
    | 0 =>
      let s := alloc.vec.Vec.deref idx
      host_commitment.Commitment.multiproof cc1 s
    | 1 =>
      let s := alloc.vec.Vec.deref idx
      host_commitment.Commitment.multiproof cc2 s
    | _ =>
      let s := alloc.vec.Vec.deref idx
      host_tree.BinaryTree.multiproof tree s)
  let r ← PV_L1_Logged.lift (core.option.Option.ok_or o verifier.Error.Allocation)
  let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let a ← PV_L1_Logged.lift (compact.SLOT_NODES)
    let i ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_mul 3#usize batch))
    let i1 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add i t))
    let i2 ← PV_L1_Logged.lift (Array.index_usize a i1)
    let cap ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_mul 32#usize i2))
    let i3 := alloc.vec.Vec.len val
    massert (i3 <= cap)
    let s := alloc.vec.Vec.deref val
    let out1 ← PV_L1_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s)
    let i4 := alloc.vec.Vec.len out1
    let i5 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add i4 cap))
    let i6 := alloc.vec.Vec.len val
    let padded ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_sub i5 i6))
    let out2 ← PV_L1_Logged.lift (alloc.vec.Vec.resize core.clone.CloneU8 out1 padded 0#u8)
    Pure.pure (core.result.Result.Ok out2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

theorem complete_result
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize) (batch : Std.Usize) (t : Std.Usize) :
  erase (produce out cc1 cc2 tree queries batch t) = prover.append_node_slot out cc1 cc2 tree queries batch t := by
  unfold produce prover.append_node_slot
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_005
