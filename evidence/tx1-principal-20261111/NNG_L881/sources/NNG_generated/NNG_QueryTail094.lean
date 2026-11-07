import NNG_FinishTail094
import NNG_QueryOccurrence094
import NNG_CheckpointReached094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_QueryTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (observer : s.observer=none) (split : s.k.val=10)
 (domain : LIBC_QueryLoop.Domain
  (LIB_Carriers.bytes s.proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,10))
 (prepared : NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (toT12 p)))
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880) :
 NNG_Reference094.query s (toT12 p) (arr toT3 g) (toT15 a) (toT14 geo) (toT13 pending) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_r8 (NNG_InstalledCalls094.calls env) s g p a geo pending)) := by
 let code := NNG_Tree094.NNG_call_4 (NNG_InstalledCalls094.calls env).c4
  s.proof p a g s.observer geo pending s.k
 let tail : core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error → Code NNG_Context094.Output := fun r=>do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue pair=>NNG_Tree094.f_s2 (NNG_InstalledCalls094.calls env) s p pair.1 pair.2
  | .Break residual=>monadLift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
 have nativeDomain : LIBC_QueryLoop.Domain
  (LIB_Carriers.bytes s.proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,s.k.val) := by
  simpa only [split] using domain
 have original := NNG_QueryOccurrence094.source env s p a g geo pending nativeDomain
 have head : LIBC_QueryLoop.child.run
  (LIB_Carriers.bytes s.proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,10) env
  (observation (NNG_StateCalls094.port (fun r=>(toT15 r.1,toT13 r.2))) (NNG_Events094.events env) code) := by
  exact Eq.mp (congrArg (fun n=>LIBC_QueryLoop.child.run
   (LIB_Carriers.bytes s.proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,n) env
   (observation (NNG_StateCalls094.port (fun r=>(toT15 r.1,toT13 r.2))) (NNG_Events094.events env) code)) split) original
 change RSL.Spec.bind _ _ env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail
  (NNG_StateCalls094.port (fun r=>(toT15 r.1,toT13 r.2)))
  NNG_Producer094.port (NNG_Events094.events env) env _ _ head
 intro r returned
 cases r with
 | Err e=>rfl
 | Ok pair=>
  rcases pair with ⟨after,out⟩
  have actual := NNG_DLawStep136.invoke_returned (NNG_Events094.events env) _ _ _ (.Ok (after,out)) returned
  have reply := head
  unfold code NNG_Tree094.NNG_call_4 at reply
  rw [NNG_InvokeGraph094.observation,NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide),actual] at reply
  change LIBC_QueryLoop.child.run
   (LIB_Carriers.bytes s.proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,10) env
   ⟨.ret (.ok (toT15 after,toT13 out)),[]⟩ at reply
  exact NNG_FinishTail094.source env s p after out observer
   (NNG_FinishDomain094.finish _ env _ _ [] domain reply)
   (NNG_CheckpointReached094.domain env s p g a after geo pending out [] domain prepared reply proofWidth publicWidth)
#print axioms source
end AspisR1.NNG_QueryTail094
