import NNG_GeometryTail094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BatchTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (folded : Array U8 32#usize)
 (input : LIBC_PreparedLaw.Args) (ep ea : List RSL.Event)
 (observer : s.observer=none) (split : s.k.val=10)
 (prepared : LIBC_PreparedLaw.law input env ⟨.ret (.ok (toT12 p),arr toT3 g),ep⟩)
 (fields : NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (toT12 p)))
 (initial : LIBC_AccNew.child.run () env ⟨.ret (.ok (toT15 a)),ea⟩)
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880)
 (domain : LIBC_BatchMerkle.Domain (NNG_BatchCall094.args s.proof p folded 0#usize)) :
 NNG_Reference094.batch s (toT12 p) (arr toT3 g) (toT15 a) (LIB_Carriers.b32 folded) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_r5 (NNG_InstalledCalls094.calls env) s g p a folded)) := by
 let code := NNG_Tree094.NNG_call_3 (NNG_InstalledCalls094.calls env).c3 s.digest s.proof p folded 0#usize s.hash
 let tail : core.result.Result Unit verifier.Error → Code NNG_Context094.Output := fun r=>do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _=>NNG_Tree094.f_markMerkle (NNG_InstalledCalls094.calls env) s g p a
  | .Break residual=>monadLift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
 have head : LIBC_BatchMerkle.child.run (NNG_BatchCall094.args s.proof p folded 0#usize) env
  (observation (NNG_StateCalls094.port id) (NNG_Events094.events env) code) := by
  unfold code NNG_Tree094.NNG_call_3
  rw [NNG_InvokeGraph094.observation,NNG_Events094.batch_call]
  exact NNG_BatchCall094.graph env s.proof p folded 0#usize domain
 change RSL.Spec.bind _ _ env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail (NNG_StateCalls094.port id)
  NNG_Producer094.port (NNG_Events094.events env) env _ _ head
 intro r returned
 cases r with
 | Err e=>rfl
 | Ok u=>
  cases u
  change NNG_Reference094.geometry s (toT12 p) (arr toT3 g) (toT15 a) env
   (observation NNG_Producer094.port (NNG_Events094.events env)
    (NNG_Tree094.f_markMerkle (NNG_InstalledCalls094.calls env) s g p a))
  unfold NNG_Tree094.f_markMerkle
  dsimp only
  rw [observer]
  change _ env (observation _ _ (NMT_CallTree.bind
   (invoke "verifier.mark" ((none : Option (verifier.Phase → Result Unit)),verifier.Phase.Merkle 0#usize) (ok ())) _))
  rw [NNG_Silent094.invoke_ok NNG_Producer094.port env _ _ _ _
   (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))]
  exact NNG_GeometryTail094.source env s p a g input ep ea observer split prepared fields initial proofWidth publicWidth
#print axioms source
end AspisR1.NNG_BatchTail094
