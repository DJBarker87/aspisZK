import LIBC_QueryLoop
import LIBC_QueryOps
import NGC_QueryPoststate
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_QueryReturned094
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- A returned loop result exposes the actual CLOSED native one-step/induction
execution, with the SAME output pair and unchanged nominal carrier. -/
theorem native (a : LIBC_QueryLoop.Args) (env : RSL.Env) (out : LIB_VCarriers.Acc)
 (pending : LIB_VCarriers.Weights) (ev : List RSL.Event)
 (domain : LIBC_QueryLoop.Domain a)
 (returned : LIBC_QueryLoop.child.run a env ⟨.ret (.ok (out,pending)),ev⟩) :
 ∃ after,Port3_NativeQueryBody.verifier.candidate.query_loop LIBC_QueryOps.ops
  (LIBC_Bytes.raw a.1) (LIBC_QueryLoop.nativeP a) (LIBC_QueryLoop.nativeA a) (LIBC_QueryLoop.nativeG a)
  none (LIBC_QueryLoop.geo a) (LIBC_QueryLoop.pending a) 10#usize=ok (.Ok (after,pending)) ∧
  out=LIBC_VStateCarriers.fromAcc after := by
 have observation := returned.2
 change RSL.Obs.mk (.ret (.ok (out,pending))) ev=
  LIB_Carriers.resultObs LIBC_QueryLoop.port [] (LIBC_QueryLoop.model a env) at observation
 have source := LIBC_QueryLoop.source a env domain
 rw [domain.1,LIBC_Usize.from_native 10#usize (by scalar_tac)] at source
 cases run : LIBC_QueryLoop.model a env with
 | fail e=>rw [run] at observation;cases congrArg RSL.Obs.exit observation
 | div=>rw [run] at observation;cases congrArg RSL.Obs.exit observation
 | ok reply=>
   rw [run] at observation source
   cases reply with
   | Err e=>cases congrArg RSL.Obs.exit observation
   | Ok pair=>
     rcases pair with ⟨after,b⟩
     have equal : (out,pending)=(LIBC_VStateCarriers.fromAcc after,b) :=
      Except.ok.inj (RSL.Exit.ret.inj (congrArg RSL.Obs.exit observation))
     have samePending : pending=b := congrArg Prod.snd equal
     subst b
     exact ⟨after,(Port3_QueryInstall.success_iff _ _).mp source.symm,congrArg Prod.fst equal⟩
#print axioms native

/-- The SAME loop preserves the invariant and reaches next=10 on a returned
Ok arm. Both facts are conclusions of the CLOSED induction. -/
theorem post (a : LIBC_QueryLoop.Args) (env : RSL.Env) (out : LIB_VCarriers.Acc)
 (pending : LIB_VCarriers.Weights) (ev : List RSL.Event)
 (domain : LIBC_QueryLoop.Domain a)
 (returned : LIBC_QueryLoop.child.run a env ⟨.ret (.ok (out,pending)),ev⟩) :
 NFS_QueryInvariant.Domain (LIBC_QueryLoop.nativeP a) 0 10 (LIBC_VStateCarriers.toAcc out) pending ∧
 (LIBC_VStateCarriers.toAcc out).next.val=10 := by
 obtain ⟨after,run,same⟩ := native a env out pending ev domain returned
 rw [LIBC_QueryOps.closed_selection] at run
 have facts := NGC_QueryPoststate.tx1 (NFS_CallerDomains.select LIBC_QueryOps.seed)
  (LIBC_Bytes.raw a.1) (LIBC_QueryLoop.nativeP a) (LIBC_QueryLoop.nativeA a) after (LIBC_QueryLoop.nativeG a)
  (LIBC_QueryLoop.geo a) (LIBC_QueryLoop.pending a) pending domain.2.2.invariant domain.2.1 run
 rw [same,LIBC_VStateCarriers.to_from_acc]
 exact facts
#print axioms post
end AspisR1.NNG_QueryReturned094
