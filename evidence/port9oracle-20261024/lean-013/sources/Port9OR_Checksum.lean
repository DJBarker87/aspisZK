import Port9OR_Bodies

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Checksum
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Complete concrete byte comparator, not just its accepted-case soundness. -/
theorem list_compare (xs ys : List U8) :
    CheckpointBytes4Ops.listEq core.cmp.PartialEqU8 xs ys=ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      change (if decide (x=y) then CheckpointBytes4Ops.listEq core.cmp.PartialEqU8 xs ys else ok false)=_
      by_cases h : x=y
      · subst y
        simp only [decide_true,if_true,ih,List.cons.injEq,true_and]
      · simp only [h,decide_false,if_false,List.cons.injEq,false_and]

theorem compare (s : Slice U8) (a : CheckpointBytes5Effect.Digest) :
    CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s a=ok (decide (s.val≠a.val)) := by
  unfold CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq
  by_cases h : s.val.length=a.val.length
  · simp only [if_pos h,list_compare,bind_tc_ok,Bool.not_decide]
  · have different : s.val≠a.val := fun eq => h (congrArg List.length eq)
    simp only [if_neg h,bind_tc_ok,Bool.not_false,decide_true,different]

def suffix (reply : State) : Slice U8 :=
  ⟨(Port9OR_Reply.digest reply).val,by have := (Port9OR_Reply.digest reply).property; scalar_tac⟩

/-- Actual installed current-reader checksum comparison: matching sampled
reply takes the decoder branch; ANY distinct reply takes rejection. -/
theorem checksum_branches (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (matchReply otherReply : State) (different : matchReply≠otherReply) :
    (Port6CK_Ops.ops reserved unwrap).ne core.cmp.PartialEqU8
      (suffix matchReply) (Port9OR_Reply.digest matchReply)=ok false ∧
    (Port6CK_Ops.ops reserved unwrap).ne core.cmp.PartialEqU8
      (suffix matchReply) (Port9OR_Reply.digest otherReply)=ok true := by
  have differentBytes : (Port9OR_Reply.digest matchReply).val≠(Port9OR_Reply.digest otherReply).val := by
    intro equal
    have equalDigest : Port9OR_Reply.digest matchReply=Port9OR_Reply.digest otherReply := Subtype.ext equal
    have equalState := congrArg CheckpointBytesDigest.stateOf equalDigest
    rw [Port9OR_Reply.state_digest,Port9OR_Reply.state_digest] at equalState
    exact different equalState
  change CheckpointBytes4Ops.ne _ _ _=_ ∧ CheckpointBytes4Ops.ne _ _ _=_
  rw [compare,compare]
  simp only [suffix,ne_eq,not_true_eq_false,decide_false,differentBytes,decide_true,and_self]

/-- The emitted source decoder tail receives the converted actual reply.
This branch keeps the inner Checkpoint error and executes no decoder suffix. -/
theorem checksum_reject (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (ck : Slice U8) (v : transport.Variant) (next : U8) (last : Usize)
    (matchReply otherReply : State) (different : matchReply≠otherReply) :
    Port4A_NativeReader.tail (Port6CK_Ops.ops reserved unwrap) ck v next last
      (suffix matchReply) (Port9OR_Reply.digest otherReply)=ok (.Err .Checkpoint) := by
  unfold Port4A_NativeReader.tail
  rw [(checksum_branches reserved unwrap matchReply otherReply different).2]
  rfl

/-- Retained counterexample schema: Port8's single-read continuation returns
native d even when the actual oracle reply differs. Port9 returns the reply. -/
theorem discarded_reply {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (parts : CheckpointBytes5Effect.Parts) (d : CheckpointBytes5Effect.Digest)
    (called : D.digest hash parts=ok d) (H : Bytes → State)
    (different : CheckpointBytesDigest.stateOf d≠H (AspisR1DigestLogCarrier.flatten parts)) :
    (eval H (Port8EFF_CheckpointCode.program D hash (.read parts .done))).2≠
      (eval H (Port9OR_Code.program D hash (.read parts .done))).2 := by
  simp only [Port8EFF_CheckpointCode.program,Port9OR_Code.program,called,
    VTop_OracleCode.continueWith,eval,ne_eq,Result.ok.injEq]
  intro same
  have h := congrArg CheckpointBytesDigest.stateOf same
  rw [Port9OR_Reply.state_digest] at h
  exact different h

#print axioms list_compare
#print axioms compare
#print axioms checksum_branches
#print axioms checksum_reject
#print axioms discarded_reply
end AspisR1.Port9OR_Checksum
end
