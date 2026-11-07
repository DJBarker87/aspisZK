import LIBB_Tx2EnvTrace
import LIBB_TagSource
import LIBB_TagStop
set_option autoImplicit false
noncomputable section
namespace LIBB_EnvCommon
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Host representation at the SAME reached records. This predicate is not
installed as an input clause: the concrete EnvRep/host bridge must prove it. -/
def Bound (env : RSL.Env)
 (records : List (Occurrence (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ())) : Prop :=
 ∀ record∈records,LIBB_RecordReservation.Bound (LIBB_Tx2Reservation.reservation env)
  record.entered record.input

/-- Exact Result and outer chronology at the partition-preserving Env model.
All Err/fail/div arms of a resolved source invocation are retained. -/
theorem resolved (env : RSL.Env) (pub proof ck : Slice U8)
 (len : proof.val.length=57607) (result : R Unit)
 (records : List (Occurrence (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()))
 (native : Invocation (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  (NLT_NativeSource.skeleton (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) pub proof ck ()) result records)
 (bound : Bound env records) :
 result=LIBB_Tx2EnvCode.common env pub proof ck ∧
 records.map actual=(LIBB_Tx2EnvCode.observed env pub proof ck).events :=
 LIBB_TagSource.source (LIBB_Tx2Reservation.reservation env) _ _ pub proof ck () len result records native bound

/-- Independent native abort keeps only its prefix and pending question.
No returned native reply or equality to a failing source result is invented. -/
theorem stopped (env : RSL.Env) (pub proof ck : Slice U8)
 (len : proof.val.length=57607)
 (records : List (Occurrence (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()))
 (cut : NLT_C04Stop.Cut (LIBB_PartitionEnv.H env))
 (native : NLT_C04Stop.At (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  (NLT_NativeSource.skeleton (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) pub proof ck ()) records cut)
 (bound : Bound env records) :
 ∃ reply suffix,(LIBB_Tx2EnvCode.observed env pub proof ck).events=
  records.map actual++Event.merkle cut.proof cut.prepared cut.folded reply::suffix :=
 LIBB_TagStop.source_prefix (LIBB_Tx2Reservation.reservation env) _ _ pub proof ck () len records cut native bound

theorem stopped_query (env : RSL.Env) (pub proof ck : Slice U8)
 (len : proof.val.length=57607) (root0 : NLP_InputDomain.Root0 ck proof)
 (records : List (Occurrence (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()))
 (cut : NLT_C04Stop.Cut (LIBB_PartitionEnv.H env))
 (native : NLT_C04Stop.At (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  (NLT_NativeSource.skeleton (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) pub proof ck ()) records cut)
 (bound : Bound env records) :
 NLL_Prefix.At
  (NLL_Parent.plan (LIBB_PartitionEnv.H env) cut.proof
   (NLP_RootCodec.parsed cut.proof (Port3_BatchStage.root1 cut.prepared))
   cut.prepared.queries 1#usize (NLL_Parent.sites (NLL_BatchSource.roots cut.prepared cut.folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV) (cut.inside++cut.pending.answered) cut.pending.parts :=
 (LIBB_TagStop.installed (LIBB_Tx2Reservation.reservation env) _ _ pub proof ck () len root0 records cut native bound).1
#print axioms resolved
#print axioms stopped
#print axioms stopped_query
end LIBB_EnvCommon
end
