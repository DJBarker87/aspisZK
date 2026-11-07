import NNG_WeightsTail094
import NNG_GeometryDomain094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_GeometryTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (input : LIBC_PreparedLaw.Args) (ep ea : List RSL.Event)
 (observer : s.observer=none) (split : s.k.val=10)
 (prepared : LIBC_PreparedLaw.law input env ⟨.ret (.ok (toT12 p),arr toT3 g),ep⟩)
 (fields : NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (toT12 p)))
 (initial : LIBC_AccNew.child.run () env ⟨.ret (.ok (toT15 a)),ea⟩)
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880) :
 NNG_Reference094.geometry s (toT12 p) (arr toT3 g) (toT15 a) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_r6 (NNG_InstalledCalls094.calls env) s g p a)) := by
 let code := NNG_Tree094.NNG_call_9 (NNG_InstalledCalls094.calls env).c9 p.queries 0#usize s.k
 let tail : core.result.Result verifier.QueryGeometry verifier.Error → Code NNG_Context094.Output := fun r=>do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue geo=>NNG_Tree094.f_r7 (NNG_InstalledCalls094.calls env) s g p a geo a.weights.deref
  | .Break residual=>monadLift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
 have domain := NNG_GeometryDomain094.reached input env _ _ ep prepared
 have nativeDomain : LIBC_Geometry.Domain (toT12 p,(0#usize).val,s.k.val) := by
  simpa only [split] using domain
 have original : LIBC_Geometry.child.run (toT12 p,(0#usize).val,s.k.val) env
  (observation (NNG_StateCalls094.port toT14) (NNG_Events094.events env) code) := by
  unfold code NNG_Tree094.NNG_call_9
  rw [NNG_InvokeGraph094.observation,NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide)]
  exact NNG_GeometryCall094.graph env p 0#usize s.k nativeDomain
 have head : LIBC_Geometry.child.run (toT12 p,0,10) env
  (observation (NNG_StateCalls094.port toT14) (NNG_Events094.events env) code) := by
  exact Eq.mp (congrArg (fun n=>LIBC_Geometry.child.run (toT12 p,0,n) env
   (observation (NNG_StateCalls094.port toT14) (NNG_Events094.events env) code)) split) original
 change RSL.Spec.bind _ _ env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail (NNG_StateCalls094.port toT14)
  NNG_Producer094.port (NNG_Events094.events env) env _ _ head
 intro r returned
 cases r with
 | Err e=>rfl
 | Ok geo=>
  have geometry := NNG_InvokeReturned094.silent env _ _ _ (core.result.Result.Ok geo) (NNG_StateCalls094.port toT14)
   (LIBC_Geometry.child.run (toT12 p,0,10)) head returned
   (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))
  exact NNG_WeightsTail094.source env s p a g geo input ep ea [] observer split prepared fields initial geometry proofWidth publicWidth
#print axioms source
end AspisR1.NNG_GeometryTail094
