import NIT_FinishInput
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_FinishLogWitness
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

/-- A returning-log witness on exactly the harness's primitive pre-state and
opaque replies. This is a cut-local construction, not a proof that actual
round/new/pair/dot calls produced these replies. That root join stays OPEN. -/
theorem exists_log (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (input : NIG_FinishInput.Domain proof v p a)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (roundReplies : Fin 2 → Reply FE) (newError : Option verifier.Error)
 (pairReply dotReply : Reply FE)
 (cr : ∀ side,replyCanonical (roundReplies side))
 (cp : replyCanonical pairReply) (cd : replyCanonical dotReply) :
 ∃ (l : FinishLog) (out : Reply Unit),
 cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out ∧
 l.round_reply=roundReplies ∧ l.new.error=newError ∧ l.pair.reply=pairReply ∧ l.dot_reply=dotReply := by
 let base : FinishLog:=⟨id,0,roundReplies,(fun side=>if side=0 then round0 else round1),
  (fun _=>224),(fun side=>NIG_FinishAlpha.alpha p side.val side.isLt),
  (fun side=>if side=0 then p.claim else match roundReplies 0 with | .Ok value=>value | .Err _=>p.claim),
  ⟨p.variant,semanticAlpha,z,none,newError,1⟩,
  ⟨owner,alpha,2,message,2048,p.kappa,pairReply,1⟩,dotReply,message,2048,weights,64⟩
 let l : FinishLog:={base with count:=(finishExpected a base).2}
 obtain ⟨s2,claim,kappa,alphas,r0,r1,size⟩:=NIT_FinishInput.primitive proof v p a input
 refine ⟨l,(finishExpected a l).1,?_,rfl,rfl,rfl,rfl⟩
 refine ⟨s2,claim,kappa,alphas,NIG_FinishAlpha.canonical _ input.accumulator.rhs,
  cr,cp,cd,r0,r1,size,input.accumulator.width,rfl,rfl,(fun _ _=>rfl),rfl,rfl,rfl,rfl,?_,
  (fun _=>⟨rfl,rfl,rfl,rfl⟩),(fun _=>⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩),(fun _=>⟨rfl,rfl,rfl,rfl⟩)⟩
 intro reached
 refine ⟨rfl,rfl,rfl,?_⟩
 cases h : roundReplies 0 with
 | Err e=>
  have count : l.count=1 := by simp only [l,base,finishExpected,h]
  omega
 | Ok value=>simp [l,base,h]

#print axioms exists_log
end AspisR1.NIT_FinishLogWitness
