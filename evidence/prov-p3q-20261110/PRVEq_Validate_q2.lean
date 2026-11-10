-- PCVQ_ item (1) leaf: the fresh VTop validate_checkpoint_queries against CheckpointBytes4Ops.validate (text-adapted copy of NJC_ValidateStep /
-- NJC_ValidatePort.loop_exact over the fresh VTop loop; the loop body is identical, only the phantom error type differs).
import Aeneas
import PRVEq_Tx2Deployed_n1
import NJC_ValidateResult
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVQ_Validate2
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1
attribute [local instance] Classical.propDecidable

abbrev VErr := AdapterRw.aspis_r1_cost_probe.verifier.Error
def pendingF : core.result.Result Unit AspisR1Stage2.verifier.Error → Option (core.result.Result Unit VErr)
 | .Ok _ => some (.Ok ())
 | .Err _ => none

theorem step (q : Array U32 22#usize) (i : Usize)
 (pre tail : List U32) (x : U32)
 (shape : q.val=pre++x::tail) (index : i.val=pre.length) :
 VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries_loop.body q i=
 if x.val≥262144 ∨ x∈pre then ok (.done none)
 else ok (.cont (Usize.wrapping_add i 1#usize)) := by
 have room : i.val<q.val.length := by rw [shape,index];simp
 obtain ⟨value,read,equal⟩ := WP.spec_imp_exists (Array.index_usize_spec q i room)
 have valueEq : value=x := by rw [equal];simp [shape,index]
 have readX := read.trans (congrArg Result.ok valueEq)
 obtain ⟨front,frontRead,contents⟩ := Port5Q2_ReaderPrefix.read q i (by omega)
 have frontEq : front.val=pre := by rw [contents,shape,index];simp
 have active : i<Slice.len (Array.to_slice q) := by change i.val<q.val.length;exact room
 have small : i.val<22 := by have size : q.val.length=22 := q.property;omega
 simp only [VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries_loop.body,
  lift,bind_tc_ok,if_pos active,readX,NJC_ValidateArithmetic.shift]
 by_cases high : x.val≥262144
 · simp only [show x≥262144#u32 from high,ite_true,high,true_or]
 · simp only [show ¬x≥262144#u32 from high,ite_false,frontRead,bind_tc_ok]
   rw [NJC_Contains.source,frontEq]
   by_cases duplicate : x∈pre
   · simp [high,duplicate]
   · simp only [duplicate,decide_false, Bool.false_eq_true,if_false,
      NJC_ValidateArithmetic.increment i small,bind_tc_ok]
     simp only [high,false_or,duplicate,if_false]

theorem loop_exact (q : Array U32 22#usize) (pre tail : List U32) (i : Usize)
 (shape : q.val=pre++tail) (index : i.val=pre.length) :
 VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries_loop q i=
 ok (pendingF (CheckpointBytes4Ops.queryLoop pre tail)) := by
 induction tail generalizing pre i with
 | nil =>
  have inactive : ¬i<Slice.len (Array.to_slice q) := by
   change ¬i.val<q.val.length
   rw [shape,index,List.append_nil]
   omega
  unfold VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries_loop.body,
   lift,bind_tc_ok,if_neg inactive,CheckpointBytes4Ops.queryLoop,pendingF]
 | cons x tail ih =>
  have step:=step q i pre tail x shape index
  unfold VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,step]
  by_cases bad : x.val≥262144 ∨ x∈pre
  · simp only [if_pos bad,CheckpointBytes4Ops.queryLoop,pendingF]
  · simp only [if_neg bad,CheckpointBytes4Ops.queryLoop]
    have small : i.val<22 := by
     have size : q.val.length=22 := q.property
     rw [shape,List.length_append,List.length_cons] at size
     omega
    have next : (Usize.wrapping_add i 1#usize).val=(pre++[x]).length := by
     rw [Port3_Wrapping.increment i (by omega),index,List.length_append,List.length_singleton]
    have shape1 : q.val=(pre++[x])++tail := by
     simpa only [List.append_assoc,List.singleton_append] using shape
    exact ih (pre++[x]) (Usize.wrapping_add i 1#usize) shape1 next

theorem validate_fresh (queries : Array U32 22#usize) :
    verifier.validate_checkpoint_queries queries =
      (do let a ← CheckpointBytes4Ops.validate queries
          ok (match a with
              | .Ok v => .Ok v
              | .Err e => .Err (Port3_CheckpointInstall.error e))) := by
  unfold verifier.validate_checkpoint_queries CheckpointBytes4Ops.validate
  rw [loop_exact queries [] queries.val 0#usize rfl rfl]
  simp only [bind_tc_ok]
  rw [NJC_ValidateResult.model]
  by_cases good : NJC_ValidateResult.ValidFrom [] queries.val
  · simp only [if_pos good, pendingF]
  · simp only [if_neg good, pendingF]; rfl

#print axioms step
#print axioms loop_exact
#print axioms validate_fresh
end PCVQ_Validate2
