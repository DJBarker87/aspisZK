-- PCVQ_ item (1): h18 for the deployed Ops. The Ext fields that PCVN left arbitrary (xdep y d) are now fixed to the deployed values (yDep),
-- and each resume leaf is related to the deployed ResumeOps leaf. Remaining explicit hypotheses are named in the theorem statements.
import Aeneas
import PRVEq_Tx2Deployed_n1
import PRVEq_Resume_q13
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVQ_Tx2Deployedq4
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1 PCVQ_Resumeq13 PCVN_Tx2Deployed

/-- Deployed values of the thirteen Ext fields that Bound does not constrain; the other ten are the Ops fields (as in xdep).
HM-B: Iter::any is the hand model NIL_FreshOps.any. HM-C: Result::map_err is NIL_FreshOps.mapError. -/
def yDep (reserved : Bool) (d : VTop_Stages.Ops) : Ext where
  Slice_Insts_CoreCmpPartialEqArray_eq := fun {T U N} inst => (CheckpointBytes4Ops.ops reserved).eq inst
  Slice_Insts_CoreCmpPartialEqArray_ne := fun {T U N} inst => (CheckpointBytes4Ops.ops reserved).ne inst
  aspis_core_field_QM31_Insts_CoreCloneClone_clone := fun x => ok x
  aspis_core_field_QM31_ZERO := (CheckpointBytes4Ops.ops reserved).zeroK
  aspis_core_field_QM31_from_le_bytes := fun s => do
    let q ← OraclePortCkptAbi2Extracted.decode_k_spec s
    ok (Option.map CheckpointBytes3Namespaces.fromK q)
  aspis_core_field_wide_exact_WideExact_from_le_bytes := @d.op2
  aspis_core_r0_heap_filled := fun {T} _ n q => do
    let out ← OraclePortStdAllocation.filled n q reserved
    match out with
    | Except.ok v => ok (core.result.Result.Ok v)
    | Except.error _ => ok (core.result.Result.Err aspis_core.r0.Error.Allocation)
  core_result_Result_map_err := @NIL_FreshOps.mapError
  core_slice_iter_Iter_Insts_CoreIterTraitsIteratorIteratorSharedAT_any := @NIL_FreshOps.any
  transport_Variant_final_len := (CheckpointBytes4Ops.ops reserved).finalLen
  transport_Variant_tag := (CheckpointBytes4Ops.ops reserved).tag
  verifier_BatchedWeights_finish := @d.op9
  verifier_BatchedWeights_new := @d.op10
  verifier_QueryGeometry_for_range := @d.op11
  verifier_candidate_batch_merkle := @d.op5
  verifier_candidate_parse_shape := @d.op3
  verifier_candidate_query_loop := @d.op6
  verifier_checkpoint_size := (CheckpointBytes4Ops.ops reserved).checkpointSize
  verifier_finish_relation := @d.op19
  verifier_mark := @d.op13
  verifier_read_checkpoint_semantic_alpha := fun b a => do
    let r ← (CheckpointBytes4Ops.ops reserved).readSemanticAlpha b a
    ok (phi r)
  verifier_read_checkpoint_weights := fun b a w => do
    let r ← (CheckpointBytes4Ops.ops reserved).readWeights b a w
    ok (phi r)
  weights_powers := @d.op17

theorem anyLoop_eq {H : Type} (D : aspis_core.digest.Digest32 H) :
    ∀ (n : Nat) (it : core.slice.iter.Iter Std.U8),
      NIL_FreshOps.anyLoop (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool D) n it ()
        = CheckpointBytes4Ops.headerLoop n it := by
  intro n
  induction n with
  | zero => intro it; rfl
  | succ n ih =>
    intro it
    simp only [NIL_FreshOps.anyLoop, CheckpointBytes4Ops.headerLoop]
    congr 1; funext p
    rcases p with ⟨value, rest⟩
    cases value with
    | none => rfl
    | some b =>
      simp only [verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool,
        verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool.call_mut, bind_tc_ok]
      change (if (b != 0#u8) = true then ok (true, rest) else
        NIL_FreshOps.anyLoop (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool D) n rest ()) =
        (if (b != 0#u8) = true then ok (true, rest) else CheckpointBytes4Ops.headerLoop n rest)
      split
      · rfl
      · exact ih rest

section
variable (reserved : Bool) (d : VTop_Stages.Ops)

theorem leaf_any {H : Type} (D : aspis_core.digest.Digest32 H) (it : core.slice.iter.Iter Std.U8) :
    (xdep (yDep reserved d) d).core_slice_iter_Iter_Insts_CoreIterTraitsIteratorIteratorSharedAT_any
      (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool D) it () =
      (CheckpointBytes4Ops.ops reserved).headerAny it := by
  change NIL_FreshOps.any _ it () = _
  unfold NIL_FreshOps.any
  rw [anyLoop_eq]; rfl

theorem leaf_raw (n : Std.Usize) (r : verifier.Reader) :
    verifier.Reader.raw n r = (CheckpointBytes4Ops.ops reserved).raw n r := rfl

theorem leaf_k {B : Type} (r : verifier.Reader)
    (K : core.result.Result aspis_core.field.QM31 VErr × verifier.Reader → Result B) :
    (verifier.Reader.k (xdep (yDep reserved d) d) r >>= K) =
      ((CheckpointBytes4Ops.ops reserved).readK r >>= fun p => K (phi p.1, p.2)) := by
  change (verifier.Reader.k (xdep (yDep reserved d) d) r >>= K) = (CheckpointBytes3Reader.readK r >>= fun p => K (phi p.1, p.2))
  unfold verifier.Reader.k CheckpointBytes3Reader.readK
  have hraw : verifier.Reader.raw 16#usize r = CheckpointBytes3Reader.raw 16#usize r := rfl
  rw [hraw]
  simp only [xdep, yDep, bind_assoc, bind_tc_ok, lift]
  congr 1; funext p
  rcases p with ⟨b, out⟩
  change ((do
      let o ← (do let q ← OraclePortCkptAbi2Extracted.decode_k_spec b.to_slice
                  ok (Option.map CheckpointBytes3Namespaces.fromK q))
      let r ← core.option.Option.ok_or o AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint
      ok (r, out)) >>= K) = ((do
      let q ← OraclePortCkptAbi2Extracted.decode_k_spec b.to_slice
      ok (CheckpointBytes3Reader.optionK q, out)) >>= fun p => K (phi p.1, p.2))
  simp only [bind_assoc, bind_tc_ok]
  congr 1; funext q
  cases q <;> rfl

theorem leaf_filled {H B : Type} (D : aspis_core.digest.Digest32 H) (n : Std.Usize) (q : aspis_core.field.QM31)
    (K : core.result.Result (alloc.vec.Vec aspis_core.field.QM31) VErr → Result B) :
    ((xdep (yDep reserved d) d).aspis_core_r0_heap_filled (aspis_core.field.QM31.Insts.CoreMarkerCopy (xdep (yDep reserved d) d)) n q >>= fun r =>
      (xdep (yDep reserved d) d).core_result_Result_map_err
        (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError D) r () >>= K)
      = ((CheckpointBytes4Ops.ops reserved).filled n q >>= fun a => K (phi a)) := by
  change _ = (CheckpointBytes3Allocation.filled reserved n q >>= fun a => K (phi a))
  simp only [xdep, yDep, CheckpointBytes3Allocation.filled, NIL_FreshOps.mapError, bind_assoc, bind_tc_ok]
  congr 1; funext out
  cases out <;> rfl
end

#print axioms anyLoop_eq
#print axioms leaf_any
#print axioms leaf_raw
#print axioms leaf_k
#print axioms leaf_filled
end PCVQ_Tx2Deployedq4
