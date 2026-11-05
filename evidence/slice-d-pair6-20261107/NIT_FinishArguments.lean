import NIT_RefInterpretation
import NIT_FinishComposition
set_option autoImplicit false
namespace AspisR1.NIT_FinishArguments
open Aeneas Aeneas.Std Result NIT_Cuts NIT_RefInterpretation AspisR1Stage2

/-- The first call is unconditionally observed; its decoded bytes and claim
are the actual finish-call inputs, not an independently chosen round packet. -/
theorem first (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit)
 (cut : cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out) :
 decode (⟨round0,v.round0⟩ : Ref (Slice U8)) (l.round_ptr 0)=some v.round0 ∧
 l.round_len 0=224 ∧ l.round_alpha 0=NIG_FinishAlpha.alpha p 0 (by decide) ∧
 l.round_claim 0=p.claim := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,ptr,len,alpha,claim,_⟩
 exact ⟨at_pointer _ _ ptr,len,alpha,claim⟩

/-- The second round's claim is precisely the first round's full successful
reply. The reachability condition is an observed call count, not success
assumed at the caller boundary. -/
theorem second (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit)
 (cut : cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out)
 (reached : 2≤l.count) :
 decode (⟨round1,v.round1⟩ : Ref (Slice U8)) (l.round_ptr 1)=some v.round1 ∧
 l.round_len 1=224 ∧ l.round_alpha 1=NIG_FinishAlpha.alpha p 1 (by decide) ∧
 l.round_reply 0=.Ok (l.round_claim 1) := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,second,_⟩
 obtain ⟨ptr,len,alpha,claim⟩ := second reached
 exact ⟨at_pointer _ _ ptr,len,alpha,claim⟩

theorem pair (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit)
 (cut : cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out)
 (reached : 4≤l.count) :
 l.pair.who=owner ∧
 decode (⟨alpha,p.alpha⟩ : Ref (Array FE 2#usize)) l.pair.alpha=some p.alpha ∧
 decode (⟨message,v.final_message⟩ : Ref (Slice U8)) l.pair.message=some v.final_message ∧
 l.pair.kappa=p.kappa := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,pair,_⟩
 obtain ⟨_,who,ap,_,msg,_,kap⟩ := pair reached
 exact ⟨who,at_pointer _ _ ap,at_pointer _ _ msg,kap⟩

theorem dot (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit)
 (cut : cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out)
 (reached : 6≤l.count) :
 decode (⟨message,v.final_message⟩ : Ref (Slice U8)) l.dot_f=some v.final_message ∧
 decode (⟨weights,a.weights⟩ : Ref (Slice aspis_core.field.QM31)) l.dot_weights=some a.weights ∧
 l.dot_f_len=2048 ∧ l.dot_len=64 := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,dot⟩
 obtain ⟨msg,len,ws,width⟩ := dot reached
 exact ⟨at_pointer _ _ msg,at_pointer _ _ ws,len,width⟩

#print axioms first
#print axioms second
#print axioms pair
#print axioms dot
end AspisR1.NIT_FinishArguments
