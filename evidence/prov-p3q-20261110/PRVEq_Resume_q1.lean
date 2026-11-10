-- PCVQ_ item (1): the fresh VTop resume (PRVEq_VTop_l1) against the gate resumeWithOps, with every leaf dependence stated.
import Aeneas
import PRVEq_Tx2Deployed_n1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVQ_Resume
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1

abbrev VErr := AdapterRw.aspis_r1_cost_probe.verifier.Error

def phi {A : Type} : core.result.Result A AspisR1Stage2.verifier.Error → core.result.Result A VErr
  | .Ok v => .Ok v
  | .Err e => .Err (Port3_CheckpointInstall.error e)

theorem ite_bind' {α β : Type} (c : Prop) [Decidable c] (a b : Result α) (K : α → Result β) :
    ((if c then a else b) >>= K) = if c then a >>= K else b >>= K := by
  split <;> rfl

/-- Every external or helper the fresh resume reads, tied to the ResumeOps leaf that the deployed reader uses. -/
structure Leaves (x : Ext) (ops : AspisR1Stage2.ResumeOps) : Prop where
  size : ∀ v, x.verifier_checkpoint_size v = ops.checkpointSize v
  tag : ∀ v, x.transport_Variant_tag v = ops.tag v
  final : ∀ v, x.transport_Variant_final_len v = ops.finalLen v
  ne : ∀ {T U : Type} {N : Std.Usize} (inst : core.cmp.PartialEq T U),
    x.Slice_Insts_CoreCmpPartialEqArray_ne (N := N) inst = ops.ne inst
  any : ∀ {H : Type} (D : aspis_core.digest.Digest32 H) (it : core.slice.iter.Iter Std.U8),
    x.core_slice_iter_Iter_Insts_CoreIterTraitsIteratorIteratorSharedAT_any
      (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool D) it () = ops.headerAny it
  raw : ∀ n r, verifier.Reader.raw n r = ops.raw n r
  k : ∀ r, verifier.Reader.k x r = (do let p ← ops.readK r; ok (phi p.1, p.2))
  e : ∀ r, verifier.Reader.e x r = (do let p ← ops.readE r; ok (phi p.1, p.2))
  validate : ∀ q, verifier.validate_checkpoint_queries q = (do let a ← ops.validate q; ok (phi a))
  sem : ∀ b a, x.verifier_read_checkpoint_semantic_alpha b a = (do let r ← ops.readSemanticAlpha b a; ok (phi r))
  weights : ∀ b a w, x.verifier_read_checkpoint_weights b a w = (do let r ← ops.readWeights b a w; ok (phi r))
  zero : x.aspis_core_field_QM31_ZERO = ops.zeroK
  filled : ∀ {H : Type} (D : aspis_core.digest.Digest32 H) (n : Std.Usize) (q : aspis_core.field.QM31),
    (do let r ← x.aspis_core_r0_heap_filled (aspis_core.field.QM31.Insts.CoreMarkerCopy x) n q
        x.core_result_Result_map_err (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError D) r ())
      = (do let a ← ops.filled n q; ok (phi a))

theorem resume_via_leaves (x : Ext) (ops : AspisR1Stage2.ResumeOps) (L : Leaves x ops)
    {H : Type} (D : aspis_core.digest.Digest32 H) (bytes proof public1 : Slice Std.U8)
    (v : transport.Variant) (hash : H) :
    verifier.resume x D bytes proof public1 v hash =
      (do let out ← AspisR1Stage2.verifier.resumeWithOps ops (VTop_Checkpoint.digest D) bytes proof public1 v hash
          ok (phi out)) := by
  unfold verifier.resume AspisR1Stage2.verifier.resumeWithOps
  simp only [bind_assoc, ite_bind', L.size, L.tag, L.ne, L.any, L.raw, L.k, L.e, L.validate, L.sem, L.weights,
    core.cmp.impls.PartialEqShared.ne, AspisR1Stage2.slicePartialEq, Slice.Insts.CoreCmpPartialEqArray,
    VTop_Checkpoint.digest]
  done
end PCVQ_Resume
