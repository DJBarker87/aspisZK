import NNX_QueryPost
import LIBC_QueryLoop
import LIBC_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_QueryOutput
open Aeneas Aeneas.Std Result AspisR1Stage2 NFG_QueryLoopDefs
abbrev run (a : LIBC_QueryLoop.Args) := NFG_QueryLoopDefs.run
 (NFS_QueryLoopRoot.child (NFS_CallerDomains.select LIBC_QueryOps.seed)
  (LIBC_Bytes.raw a.1) (LIBC_QueryLoop.nativeP a) (LIBC_QueryLoop.nativeG a)
  (LIBC_QueryLoop.geo a) 0 0)
 10#usize 10 (.Ok (LIBC_QueryLoop.nativeA a,LIBC_QueryLoop.pending a))

theorem source (a : LIBC_QueryLoop.Args) (env : RSL.Env)
 (after : LIB_VCarriers.Acc) (pending : LIB_VCarriers.Weights)
 (called : LIBC_QueryLoop.value a env = .ok (after,pending)) :
 run a = .ok (.Ok (LIBC_VStateCarriers.toAcc after,pending)) := by
 unfold LIBC_QueryLoop.value LIBC_QueryLoop.model at called
 change LIBC_ResultGraph.value LIBC_QueryLoop.port (.error .Query)
  (Port3_QueryInstall.result (run a)) = .ok (after,pending) at called
 cases h : run a with
 | fail e => rw [h] at called;cases called
 | div => rw [h] at called;cases called
 | ok reply =>
  cases reply with
  | Err e => rw [h] at called;cases called
  | Ok pair =>
   rcases pair with ⟨native,b⟩
   rw [h] at called
   have image : (LIBC_VStateCarriers.fromAcc native,b) = (after,pending) := Except.ok.inj called
   cases image
   rw [LIBC_VStateCarriers.to_from_acc]
   exact h

theorem domain (a : LIBC_QueryLoop.Args) (env : RSL.Env)
 (d : LIBC_QueryLoop.Domain a) (after : LIB_VCarriers.Acc) (pending : LIB_VCarriers.Weights)
 (called : LIBC_QueryLoop.value a env = .ok (after,pending)) :
 LIBC_Finish.Domain (pending,after) := by
 have native := source a env after pending called
 have same := NFS_QueryLoopRoot.finite (NFS_CallerDomains.select LIBC_QueryOps.seed)
  (LIBC_Bytes.raw a.1) (LIBC_QueryLoop.nativeP a) (LIBC_QueryLoop.nativeG a)
  (LIBC_QueryLoop.geo a) 0 0 0 10#usize (by decide) d.2.2.gCanonical 10
  (.Ok (LIBC_QueryLoop.nativeA a,LIBC_QueryLoop.pending a)) d.2.2.invariant
 have output := same.symm.trans native
 exact ⟨LIBC_QueryLoop.nativeP a,0,10,
  NNX_QueryPost.finite _ _ _ _ _ 0 10#usize (by decide) 10 _ d.2.2.invariant (LIBC_VStateCarriers.toAcc after) pending output⟩
#print axioms source
#print axioms domain
end AspisR1.NNX_QueryOutput
end
