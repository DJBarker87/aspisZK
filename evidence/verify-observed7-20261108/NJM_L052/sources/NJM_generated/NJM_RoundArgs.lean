import NJM_RoundAdmissible
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundArgs
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames
attribute [local instance] Classical.propDecidable

/-- K073/K074 at the SAME source arguments, including the post-challenge alpha
read. All coefficients/alpha/transcript cells are universally observed windows.
Pointer remains an identity token of this borrowed frame, not a payload proof. -/
theorem success {H : Type} (template : RoundPre) (record : r1_wire.ValidatedRecord)
 (polynomial : Polynomial) (b running : Q) (same : b=running) (a : Alpha) (r : Usize) (bound : r.val<10)
 (before after : r1_wire.SemanticTranscript H) (q value : Q) (pointer : Nat)
 (k : Fin 28) (j : Fin 10) (z : Fin 32) (log : RoundLog)
 (cut : roundArgs (NJM_RoundStage.install {template with count:=0} record polynomial b running a r before after (.Ok q) value) pointer k j z log) :
 log.getterPrefix 0=template.prefixToken ∧ log.getterRow 0=15+r.val ∧
 log.getterCount=2 ∧ log.getterPrefix 1=template.prefixToken ∧ log.getterRow 1=15+r.val ∧
 log.decodeRow=15+r.val ∧ log.decodePointer=pointer ∧ log.decodeLength=record.framed.val.length ∧
 log.decodeOffset=0 ∧ log.boundaryValue=cell polynomial k ∧
 log.semanticRow=15+r.val ∧ log.semanticPointer=some pointer ∧
 log.semanticLength=record.framed.val.length ∧ cell log.semanticState z=cell before.state z ∧
 log.semanticNext=before.next_row ∧ log.valuePolynomial=cell polynomial k ∧
 log.valueAlpha=cell (a.set r q) j ∧ log.valueRound=r.val ∧
 log.times 0=0 ∧ log.times 1=1 ∧ log.times 2=2 ∧ log.times 3=3 ∧ log.count=4 ∧ log.frame=template.frame := by
 let s:=NJM_RoundStage.install {template with count:=0} record polynomial b running a r before after (.Ok q) value
 have dec : decoded s=true := rfl
 have sampled : NIX_CertificateFrames.sampled s=true := by simp [NIX_CertificateFrames.sampled,s,NJM_RoundStage.install,same,decoded]
 have finished : NIX_CertificateFrames.finished s=true := by
  change NIX_CertificateFrames.sampled s && true = true
  rw [sampled]
  rfl
 have alpha := congrArg (fun (ar : Alpha)=>cell ar j) (NJM_RoundNative.alpha s q bound rfl)
 rw [NJG_RoundResult.alpha_cell] at alpha
 change roundArgs s pointer k j z log at cut
 simp only [roundArgs,sampled,dec,finished,if_true] at cut
 rcases cut with ⟨dom,gp0,gr0,gc,gp1,gr1,dr,dp,dl,doff,t0,frame,bv,t1,sr,sp,sl,ss,sn,t2,vp,va,vr,t3,count⟩
 simp only [s,NJM_RoundStage.install,polyCell] at gp0 gr0 gc gp1 gr1 dr dp dl doff t0 frame bv t1 sr sp sl ss sn t2 vp va vr t3 count
 have count' : log.count=4 := by simpa only [same,decide_true,Bool.not_true,Bool.false_eq_true,if_false,Nat.zero_add] using count
 have va' : log.valueAlpha=cell (a.set r q) j := va.trans alpha
 exact ⟨gp0,gr0,gc,gp1,gr1,dr,dp,dl,doff,bv,sr,sp,sl,ss,sn,vp,va',vr,t0,t1,t2,t3,count',frame⟩

#print axioms success
end AspisR1.NJM_RoundArgs
end
