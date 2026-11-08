import NNG_FoldedTail094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_AccumulatorTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (input : LIBC_PreparedLaw.Args) (ep : List RSL.Event)
 (observer : s.observer=none) (split : s.k.val=10)
 (prepared : LIBC_PreparedLaw.law input env ⟨.ret (.ok (toT12 p),arr toT3 g),ep⟩)
 (fields : NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (toT12 p)))
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880)
 (root0 root1 : Array U8 32#usize)
 (roots : (toT12 p).roots=Array.make 2#usize [root0,root1])
 (first : root0.val=(s.proof.val.drop 16).take 32) :
 NNG_Reference094.afterPrepare s (toT12 p,arr toT3 g) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_r3 (NNG_InstalledCalls094.calls env) s g p)) := by
 let code := NNG_Tree094.NNG_call_10 (NNG_InstalledCalls094.calls env).c10 transport.Variant.S2
 let tail : core.result.Result verifier.Accumulator verifier.Error → Code NNG_Context094.Output := fun r=>do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue a=>NNG_Tree094.f_markPrepare (NNG_InstalledCalls094.calls env) s g p a
  | .Break residual=>monadLift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
 have head := NNG_StateOccurrences094.accumulator env transport.Variant.S2
 change RSL.Spec.bind _ _ env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail (NNG_StateCalls094.port toT15)
  NNG_Producer094.port (NNG_Events094.events env) env _ _ head
 intro r returned
 cases r with
 | Err e=>rfl
 | Ok a=>
  have initial := NNG_InvokeReturned094.silent env _ _ _ (core.result.Result.Ok a) (NNG_StateCalls094.port toT15)
   (LIBC_AccNew.child.run ()) head returned
   (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))
  change NNG_Reference094.afterNew s (toT12 p) (arr toT3 g) (toT15 a) env
   (observation NNG_Producer094.port (NNG_Events094.events env)
    (NNG_Tree094.f_markPrepare (NNG_InstalledCalls094.calls env) s g p a))
  unfold NNG_Tree094.f_markPrepare
  dsimp only
  rw [observer]
  change NNG_Reference094.afterNew s (toT12 p) (arr toT3 g) (toT15 a) env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind
   (invoke "verifier.mark" ((none : Option (verifier.Phase → Result Unit)),verifier.Phase.Prepare) (ok ())) _))
  rw [NNG_Silent094.invoke_ok NNG_Producer094.port env _ _ _ _
   (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))]
  exact NNG_FoldedTail094.source env s p a g input ep [] observer split prepared fields initial
   proofWidth publicWidth root0 root1 roots first
#print axioms source
end AspisR1.NNG_AccumulatorTail094
