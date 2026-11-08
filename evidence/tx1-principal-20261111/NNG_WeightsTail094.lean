import NNG_QueryTail094
import NNG_StateOccurrences094
import NNG_InvokeReturned094
import NNG_QueryDomain094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_WeightsTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (input : LIBC_PreparedLaw.Args) (ep ea eg : List RSL.Event)
 (observer : s.observer=none) (split : s.k.val=10)
 (prepared : LIBC_PreparedLaw.law input env ⟨.ret (.ok (toT12 p),arr toT3 g),ep⟩)
 (fields : NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (toT12 p)))
 (initial : LIBC_AccNew.child.run () env ⟨.ret (.ok (toT15 a)),ea⟩)
 (geometry : LIBC_Geometry.child.run (toT12 p,0,10) env ⟨.ret (.ok (toT14 geo)),eg⟩)
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880) :
 NNG_Reference094.weights s (toT12 p) (arr toT3 g) (toT15 a) (toT14 geo) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_r7 (NNG_InstalledCalls094.calls env) s g p a geo a.weights.deref)) := by
 let code := NNG_Tree094.NNG_call_8 (NNG_InstalledCalls094.calls env).c8 a.weights.deref
 let tail : core.result.Result verifier.BatchedWeights verifier.Error → Code NNG_Context094.Output := fun r=>do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue b=>NNG_Tree094.f_r8 (NNG_InstalledCalls094.calls env) s g p a geo b
  | .Break residual=>monadLift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
 have domain := NNG_AccumulatorDomain094.weights_domain env (toT15 a) ea initial
 have head := NNG_StateOccurrences094.weights env a domain
 change RSL.Spec.bind _ _ env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail (NNG_StateCalls094.port toT13)
  NNG_Producer094.port (NNG_Events094.events env) env _ _ head
 intro r returned
 cases r with
 | Err e=>rfl
 | Ok b=>
  have weights := NNG_InvokeReturned094.silent env _ _ _ (core.result.Result.Ok b) (NNG_StateCalls094.port toT13)
   (LIBC_WeightsNew.child.run (toT15 a)) head returned
   (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))
  exact NNG_QueryTail094.source env s p a g geo b observer split
   (NNG_QueryDomain094.reached _ proofWidth input env _ _ _ _ _ ep ea eg [] prepared initial geometry weights)
   fields proofWidth publicWidth
#print axioms source
end AspisR1.NNG_WeightsTail094
