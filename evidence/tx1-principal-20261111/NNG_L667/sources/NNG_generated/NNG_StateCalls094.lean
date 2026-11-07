import NNG_Carriers094
import NNG_ParseCall094
import LIBC_AccNew
import LIBC_WeightsNew
import LIBC_Geometry
import LIBC_QueryLoop
import LIBC_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_StateCalls094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094

def fromReply {A B : Type} (f : A → B) :
 core.result.Result A LIB_VCarriers.VErr → core.result.Result B verifier.Error
 | .Ok a=>.Ok (f a) | .Err e=>.Err (NNG_ParseCall094.errorBack e)
def port {A B : Type} (f : A → B) :
 core.result.Result A verifier.Error → Except LIB_VCarriers.VErr B
 | .Ok a=>.ok (f a) | .Err e=>.error (NNG_ParseCall094.error e)

theorem port_reply {A B C : Type} (f : A → B) (g : B → C)
 (r : core.result.Result A LIB_VCarriers.VErr) :
 port g (fromReply f r)=match r with | .Ok a=>.ok (g (f a)) | .Err e=>.error e := by
 cases r with
 | Ok a=>rfl
 | Err e=>exact congrArg Except.error (NNG_ParseCall094.error_inverse e)
#print axioms port_reply

theorem obs_outer {A B C : Type} (f : A → B) (g : B → C) (h : A → C)
 (same : ∀ a,g (f a)=h a) (r : Result A) (ev : List RSL.Event) :
 LIB_Carriers.resultObs g ev (NMP_ResultTransport.outer f r)=LIB_Carriers.resultObs h ev r := by
 cases r with
 | ok a=>exact congrArg (fun x=>RSL.Obs.mk (RSL.Exit.ret x) ev) (same a)
 | fail e=>rfl
 | div=>rfl
#print axioms obs_outer

def accNew (env : RSL.Env) : Result (core.result.Result verifier.Accumulator verifier.Error) :=
 NMP_ResultTransport.outer (fromReply (fromT15 ∘ LIBC_VStateCarriers.fromAcc)) (LIBC_AccNew.model env)

theorem accNew_graph (env : RSL.Env) :
 LIBC_AccNew.child.run () env
 (LIB_Carriers.resultObs (port toT15) [] (accNew env)) := by
 refine ⟨True.intro,?_⟩
 apply (LIBC_AccNew.graph env _).mpr
 apply obs_outer
 intro r
 rw [port_reply]
 cases r <;> simp only [Function.comp_apply,fromT15_inverse,LIBC_AccNew.port]
#print axioms accNew_graph

def weightsNew (env : RSL.Env) (weights : Slice aspis_core.field.QM31) :
 Result (core.result.Result verifier.BatchedWeights verifier.Error) :=
 NMP_ResultTransport.outer (fromReply fromT13)
  (Port3_PendingInstall.pending env.reservation
    ((LIBC_VStateCarriers.mapVec LIBC_VStateCarriers.q
      (⟨weights.val.map toT1,by simpa only [List.length_map] using weights.property⟩ : alloc.vec.Vec LIB_VCarriers.K))).deref))

def geometry (env : RSL.Env) (queries : Array U32 22#usize) (start finish : Usize) :
 Result (core.result.Result verifier.QueryGeometry verifier.Error) :=
 NMP_ResultTransport.outer (fromReply fromT14)
  (Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted queries start finish)

def queryLoop (env : RSL.Env) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (finish : Usize) :
 Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error) :=
 NMP_ResultTransport.outer (fromReply (fun r=>(fromT15 (LIBC_VStateCarriers.fromAcc r.1),fromT13 r.2)))
  (LIBC_QueryLoop.model (LIB_Carriers.bytes proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,finish.val) env)

theorem queryLoop_graph (env : RSL.Env) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (finish : Usize)
 (domain : LIBC_QueryLoop.Domain (LIB_Carriers.bytes proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,finish.val)) :
 LIBC_QueryLoop.child.run (LIB_Carriers.bytes proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,finish.val) env
 (LIB_Carriers.resultObs (port (fun r=>(toT15 r.1,toT13 r.2))) []
  (queryLoop env proof p a g geo pending finish)) := by
 refine ⟨domain,?_⟩
 apply (LIBC_QueryLoop.graph _ env _).mpr
 apply obs_outer
 intro r
 rw [port_reply]
 cases r <;> simp only [fromT15_inverse,fromT13_inverse,LIBC_QueryLoop.port]
#print axioms queryLoop_graph
end AspisR1.NNG_StateCalls094
