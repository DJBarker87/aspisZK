import NNG_ScanTail094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ParseTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136

def reference (a : NNG_Input094.Args) (obs : RSL.Observer) (env : RSL.Env) : RSL.RE LIB_VCarriers.VErr RSL.Bytes :=
 RSL.RE.seq (LIB_Instances.VL.parseShape.run a.proof)
  (RSL.RE.seq (LIB_Instances.VL.canonicalScan.run a.proof)
   (NNG_ReferenceMatch094.original a))

theorem source (a : NNG_Input094.Args) (obs : RSL.Observer) (env : RSL.Env)
 (own : RSL.TX1_094.Domain LIB_Instances.VL a obs a.public_) (split : a.k=10) :
 reference a obs env env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_r (NNG_InstalledCalls094.calls env) (NNG_Input094.input a obs env))) := by
 let s := NNG_Input094.input a obs env
 let code := NNG_Tree094.NNG_call_1 (NNG_InstalledCalls094.calls env).c1 s.proof
 let tail : core.result.Result transport.Variant verifier.Error → Code NNG_Context094.Output := fun r=>do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _=>NNG_Tree094.f_r1 (NNG_InstalledCalls094.calls env) s
  | .Break residual=>monadLift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
 have head : LIB_Instances.VL.parseShape.run a.proof env
  (observation NNG_ParseCall094.port (NNG_Events094.events env) code) := by
  unfold code NNG_Tree094.NNG_call_1
  rw [NNG_InvokeGraph094.observation,NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide)]
  exact NNG_ParseOriginal094.occurrence a.proof env
 change RSL.Spec.bind _ _ env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail NNG_ParseCall094.port
  NNG_Producer094.port (NNG_Events094.events env) env _ _ head
 intro r returned
 cases r with
 | Err e=>rfl
 | Ok variant=>
  have parsed := NNG_InvokeReturned094.silent env _ _ _ (core.result.Result.Ok variant) NNG_ParseCall094.port
   (LIB_Instances.VL.parseShape.run a.proof) head returned
   (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))
  exact NNG_ScanTail094.source a obs env own split [] parsed
#print axioms source
end AspisR1.NNG_ParseTail094
