import NNH_MerkleBatchTrace
import NNH_064SourceInputs
import NNC_RecordTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064SourceDetails
open Aeneas Aeneas.Std VTop_Stages NJU_CommonObserved NLT_NativeInvocation
open NNC_DigestTrace

def detail (env : RSL.Env) (e : Event) (i : NLT_NativeWindows.Input e) :
 NLT_Subcuts.Detail (LIBB_PartitionEnv.H env)
  (NLT_NativeWindows.window (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () e i) := by
 cases e with
 | merkle pr p folded reply =>
   exact .returning pr p folded _
    (NNH_MerkleBatchExecute.run (LIBB_PartitionEnv.H env) pr p folded 1#usize).1
    (NNH_MerkleBatchExecute.run (LIBB_PartitionEnv.H env) pr p folded 1#usize).2
    (NNH_MerkleBatchExecute.native (LIBB_PartitionEnv.H env) pr p folded 1#usize)
 | resume c pr pu reply => exact .ordinary _ (by intro pr p folded reply same; cases same)
 | powers gamma reply => exact .ordinary _ (by intro pr p folded reply same; cases same)
 | inactive bytes reply => exact .ordinary _ (by intro pr p folded reply same; cases same)
 | geometry queries next reply => exact .ordinary _ (by intro pr p folded reply same; cases same)
 | pending weights reply => exact .ordinary _ (by intro pr p folded reply same; cases same)
 | query pr p a g geo pending reply => exact .ordinary _ (by intro pr p folded reply same; cases same)
 | flush pending weights reply => exact .ordinary _ (by intro pr p folded reply same; cases same)
 | finish v p a reply => exact .ordinary _ (by intro pr p folded reply same; cases same)

def record (env : RSL.Env) (pub proof ck : Slice U8) (e : Event)
 (entered : e∈(LIBB_Tx2EnvCode.observed env pub proof ck).events) :
 Occurrence (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () :=
 ⟨e,NNH_064SourceInputs.input env pub proof ck e entered,
  detail env e (NNH_064SourceInputs.input env pub proof ck e entered)⟩

def trace (env : RSL.Env) : Event → Trace
 | .resume ck proof pub _ =>
   (NNC_ResumeEvents.queries (NLT_NativeWindows.resumeRun
    (LIBB_PartitionEnv.digest env) ck proof pub () (LIBB_Tx2Reservation.reservation env)).events).map Step.attempted
 | .merkle pr p folded _ =>
   (NNH_MerkleBatchTrace.calls (LIBB_PartitionEnv.H env) pr p.queries 1#usize
    (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV).map Step.attempted
 | _ => []

theorem source (env : RSL.Env) (pub proof ck : Slice U8) (e : Event)
 (entered : e∈(LIBB_Tx2EnvCode.observed env pub proof ck).events) :
 NNC_RecordTrace.FromRecord (record env pub proof ck e entered) (trace env e) := by
 cases e with
 | merkle pr p folded reply =>
   exact ⟨_,NNH_MerkleBatchTrace.native (LIBB_PartitionEnv.H env) pr p.queries 1#usize
    (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV,rfl⟩
 | resume c pr pu reply => rfl
 | powers gamma reply => rfl
 | inactive bytes reply => rfl
 | geometry queries next reply => rfl
 | pending weights reply => rfl
 | query pr p a g geo pending reply => rfl
 | flush pending weights reply => rfl
 | finish v p a reply => rfl
#print axioms detail
#print axioms source
end AspisR1.NNH_064SourceDetails
