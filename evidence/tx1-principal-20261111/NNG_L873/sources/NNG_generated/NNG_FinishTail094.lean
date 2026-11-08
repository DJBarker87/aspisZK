import NNG_CheckpointTail094
import NNG_Reference094
import NNG_DLawStep136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights)
 (observer : s.observer=none)
 (finishDomain : LIBC_Finish.Domain (toT13 pending,toT15 a))
 (checkpointDomain : LIBC_Checkpoint.Domain (NNG_CheckpointCall094.args p
  {a with weights:=⟨(NNG_FlushCall094.output pending).val,(NNG_FlushCall094.output pending).property⟩}
  s.proof s.publicBytes)) :
 NNG_Reference094.finish s (toT12 p) (toT15 a,toT13 pending) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_s2 (NNG_InstalledCalls094.calls env) s p a pending)) := by
 let decode : Slice aspis_core.field.QM31 → LIB_VCarriers.Acc := fun x=>
  toT15 {a with weights:=⟨x.val,x.property⟩}
 let code := NNG_Tree094.NNG_call_7 (NNG_InstalledCalls094.calls env).c7 pending a.weights.deref
 have head : LIBC_Finish.child.run (toT13 pending,toT15 a) env
  (observation decode (NNG_Events094.events env) code) := by
  unfold code NNG_Tree094.NNG_call_7
  rw [NNG_InvokeGraph094.observation,NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide)]
  exact NNG_FlushCall094.graph env pending a finishDomain
 have lifted := NNG_MapObservation094.mapped decode
  (Except.ok : LIB_VCarriers.Acc → Except LIB_VCarriers.VErr LIB_VCarriers.Acc)
  (NNG_Events094.events env) code env _ head
 change RSL.Spec.bind (RSL.RE.lift (LIBC_Finish.child.run (toT13 pending,toT15 a))) _ env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NMT_CallTree.bind code (fun x=>NNG_Tree094.f_bytes (NNG_InstalledCalls094.calls env) s p a ⟨x.val,x.property⟩)))
 apply NNG_SourceStep136.bind_sound code _ (fun x=>Except.ok (decode x))
  NNG_Producer094.port (NNG_Events094.events env) env _ _ lifted
 intro x returned
 have actual : NNG_FlushCall094.call pending a.weights.deref=ok x :=
  NNG_DLawStep136.invoke_returned (NNG_Events094.events env) _ _ _ x returned
 have equal : NNG_FlushCall094.output pending=x := Result.ok.inj actual
 subst x
 exact NNG_CheckpointTail094.source env s p a _ observer checkpointDomain
#print axioms source
end AspisR1.NNG_FinishTail094
