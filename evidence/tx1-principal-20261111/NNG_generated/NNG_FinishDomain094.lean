import NNG_QueryReturned094
import LIBC_Finish
import NGC_WriterDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishDomain094
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem finish (a : LIBC_QueryLoop.Args) (env : RSL.Env) (out : LIB_VCarriers.Acc)
 (pending : LIB_VCarriers.Weights) (ev : List RSL.Event)
 (domain : LIBC_QueryLoop.Domain a)
 (returned : LIBC_QueryLoop.child.run a env ⟨.ret (.ok (out,pending)),ev⟩) :
 LIBC_Finish.Domain (pending,out) := by
 have post := NNG_QueryReturned094.post a env out pending ev domain returned
 exact ⟨LIBC_QueryLoop.nativeP a,0,10,post.1⟩
#print axioms finish

/-- The exact field-value flush is the SAME actual source update whose
writer format invariant follows from the returned loop. -/
theorem writer (a : LIBC_QueryLoop.Args) (env : RSL.Env) (out : LIB_VCarriers.Acc)
 (pending : LIB_VCarriers.Weights) (ev : List RSL.Event)
 (domain : LIBC_QueryLoop.Domain a)
 (prepared : NGC_PreparationBoundary.Fields (LIBC_QueryLoop.nativeP a))
 (returned : LIBC_QueryLoop.child.run a env ⟨.ret (.ok (out,pending)),ev⟩) :
 NGC_KNE_Caller.WriterDomain (CheckpointBytes3Namespaces.toPrepared (LIBC_QueryLoop.nativeP a))
  (CheckpointBytes3Namespaces.toAccumulator (LIBC_VStateCarriers.toAcc (LIBC_Finish.value (pending,out) env))) := by
 have post := NNG_QueryReturned094.post a env out pending ev domain returned
 obtain ⟨flushed,run,writer,_,_,_⟩ := NGC_WriterDomain.after_finish (LIBC_QueryLoop.nativeP a)
  (LIBC_VStateCarriers.toAcc out) pending post.1 post.2 prepared
 have source := LIBC_Finish.source (pending,out) env (finish a env out pending ev domain returned)
 rw [run,bind_tc_ok] at source
 have value := congrArg LIBC_VStateCarriers.toAcc (Result.ok.inj source)
 rw [LIBC_VStateCarriers.to_from_acc] at value
 exact Eq.mp (congrArg (fun acc=>NGC_KNE_Caller.WriterDomain
  (CheckpointBytes3Namespaces.toPrepared (LIBC_QueryLoop.nativeP a))
  (CheckpointBytes3Namespaces.toAccumulator acc)) value) writer
#print axioms writer
end AspisR1.NNG_FinishDomain094
