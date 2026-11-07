import NNG_ProducerFull094
import NNG_AccumulatorTail094
import NNG_PrepareReturned094
import NNG_InputTransport094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

def args (s : NNG_Context094.Parent Unit) : NNG_PrepareInput087.Args :=
 ⟨toT9 s.publicValue,LIB_Carriers.bytes s.proof,LIB_Instances.VL.zeroE29⟩

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (digest : s.digest=NNG_PrepareTransport094.digest env)
 (observer : s.observer=none) (split : s.k.val=10)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL (args s) none)
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880) :
 NNG_Reference094.prepare s env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_PrepareTree094.f_r2 (NNG_InstalledCalls094.calls env) s (arr fromT3 LIB_Instances.VL.zeroE29))) := by
 let a := args s
 let code := NNG_PrepareTree094.NNG_call_5 (NNG_InstalledCalls094.calls env).c5 s.digest s.publicValue s.proof
  s.hash s.observer (arr fromT3 LIB_Instances.VL.zeroE29)
 let tail : (core.result.Result verifier.Prepared verifier.Error × Array aspis_core.field.wide_exact.WideExact 29#usize) → Code NNG_Context094.Output := fun r=>do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r.1
  match cf with
  | .Continue p=>NNG_Tree094.f_r3 (NNG_InstalledCalls094.calls env) s r.2 p
  | .Break residual=>monadLift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
 have samePublic : fromT9 a.public_=s.publicValue := toT9_inverse _
 have sameProof : NNG_Data137.bytes a.proof=s.proof := by
  rw [NNG_InputTransport094.bytes]
  exact LIBC_Bytes.from_native s.proof
 have sameG : a.g=LIB_Instances.VL.zeroE29 := rfl
 have sameHash : s.hash=() := Subsingleton.elim _ _
 have head : RSL.Spec.call (fun x : NNG_PrepareInput087.Args=>RSL.TX1_087.Domain LIB_Instances.VL x none)
  (RSL.TX1_087.Ref LIB_Instances.VL LIB_Instances.P) a env
  (observation NNG_PrepareTransport094.port (NNG_Events094.events env) code) := by
  have original := NNG_PrepareGraph094.occurrence a env domain
  simpa only [code,NNG_Tree094.NNG_call_5,←digest,←observer,samePublic,sameProof] using original
 have mapped := NNG_MapObservation094.mapped NNG_PrepareTransport094.port NNG_Reference094.normalized
  (NNG_Events094.events env) code env _ head
 change RSL.Spec.bind _ _ env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail
  (fun r=>NNG_Reference094.normalized (NNG_PrepareTransport094.port r))
  NNG_Producer094.port (NNG_Events094.events env) env _ _ mapped
 intro r returned
 rcases r with ⟨reply,g⟩
 cases reply with
 | Err e=>rfl
 | Ok p=>
  have actual := NNG_DLawStep136.invoke_returned (NNG_Events094.events env) _ _ _ (core.result.Result.Ok p,g) returned
  have canonical : NNG_PrepareAdapter094.call env (NNG_PrepareTransport094.digest env) (fromT9 a.public_)
   (NNG_Data137.bytes a.proof) () none (arr fromT3 a.g)=ok (.Ok p,g) := by
   simpa only [NNG_InstalledCalls094.calls,NNG_ConcreteCalls094.calls,←digest,←observer,samePublic,sameProof,sameG,sameHash] using actual
  obtain ⟨input,ep,prepared,fields,root0,root1,roots,first⟩ := NNG_PrepareReturned094.returned a env domain p g canonical
  have bytesSame : (NNG_PrepareInput087.input a none env).bytes=s.proof := sameProof
  rw [bytesSame] at first
  exact NNG_AccumulatorTail094.source env s p g input ep observer split prepared fields proofWidth publicWidth root0 root1 roots first
#print axioms source
end AspisR1.NNG_PrepareTail094
