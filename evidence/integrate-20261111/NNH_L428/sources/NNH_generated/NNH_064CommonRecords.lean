import NNH_064ProgramRecords
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064CommonRecords
open Aeneas Aeneas.Std VTop_Stages NJU_CommonObserved NLT_NativeInvocation
abbrev program (env : RSL.Env) (pub proof ck : Slice U8) :=
 NKE_CommonProgram.run (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
  (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
  (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env))
  (LIBB_PartitionEnv.digest env) pub proof ck () none

def record (env : RSL.Env) (pub proof ck : Slice U8) (e : Event)
 (entered : e∈(NKE_Free.eval (program env pub proof ck)).events) :=
 NNH_064SourceDetails.record env pub proof ck e (by
  rw [NKE_CommonEval.source] at entered; exact entered)

def records (env : RSL.Env) (pub proof ck : Slice U8) :=
 (NKE_Free.eval (program env pub proof ck)).events.pmap
  (fun e h=>record env pub proof ck e h) (fun _ h=>h)

theorem native (env : RSL.Env) (pub proof ck : Slice U8) (len : proof.val.length=57607) :
 Invocation (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  (program env pub proof ck) (NKE_Free.eval (program env pub proof ck)).result
  (records env pub proof ck) := by
 apply NNH_064ProgramRecords.execute
 · intro e h
   exact NNH_064SourceInputs.actual env pub proof ck len e _
 · intro e h; rfl

theorem skeleton (env : RSL.Env) (pub proof ck : Slice U8) (len : proof.val.length=57607) :
 NLT_CompleteRoot.Native (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
 pub proof ck () (.resolved (NKE_Free.eval (program env pub proof ck)).result (records env pub proof ck)) := by
 apply NLT_ReseedTransport.forward (program env pub proof ck) _
  (NLT_Reseed.source (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
   (.Ok ()) (.Ok ()) (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
   (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env)) (NLB_Parent.finish (.Ok ()))
   (LIBB_PartitionEnv.digest env) pub proof ck ())
 exact native env pub proof ck len
#print axioms native
#print axioms skeleton
end AspisR1.NNH_064CommonRecords
