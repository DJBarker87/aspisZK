import NLH_TermCompositionSource
import NLH_TermPartsFactor
import NKR_TermCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermPartsSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal

def validated (pub : Public) (out : NKR_TermTail.Output) : Result (core.result.Result NKR_TermTail.Output NKR_TermTail.Error) := do
 let result←validate_transition pub
 match result with
 | .Err error=>ok (.Err error)
 | .Ok _=>ok (.Ok out)

/--263 full emitted source Result, actual composition child and every suffix
field law internally discharged. Neither rejectedamount nor validationerror
is removed by an accepted-only premise. SOURCE SUPPORT pending native237. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point zc : Array NQ 10#usize)
 (lambda chi theta mu : NQ) (hd : NKR_DigestChildren.Domain pub)
 (hc : canonical claims) (hp : canonical point) (hz : canonical zc)
 (hl : Canon lambda) (hchi : Canon chi) (ht : Canon theta) (hm : Canon mu)
 (asset : pub.asset_id.val<2147483647) :
 (NLH_TermAmount.invalid pub.withdrawal_amount=true ∧
  terminal_parts pub claims point lambda chi theta zc mu=ok (.Err .InvalidPublicAmount)) ∨
 ∃ out : NKR_TermTail.Output,NLH_TermAmount.invalid pub.withdrawal_amount=false ∧
  terminal_parts pub claims point lambda chi theta zc mu=validated pub out ∧
  Canon out.1 ∧ canonical out.2.1 ∧ canonical out.2.2.1 ∧ Canon out.2.2.2 := by
 rcases NLH_TermCompositionSource.source pub claims point lambda chi theta hd hc hp hl hchi ht asset with rejected|accepted
 · rcases rejected with ⟨bad,comp⟩
   refine Or.inl ⟨bad,?_⟩
   rw [NLH_TermPartsFactor.source]
   unfold NLH_TermPartsFactor.reference
   rw [comp,bind_tc_ok]
   rfl
 · rcases accepted with ⟨child,good,comp,cc,cg,ch,ca,cz,cm⟩
   obtain ⟨c,tail,cut,co⟩:=NKR_TermCut.source zc point mu child hz hp hm cc ch ca
   let out : NKR_TermTail.Output:=(c.out,child.2.1,child.2.2.1,child.2.2.2.1)
   refine Or.inr ⟨out,good,?_,co,cz,cm,cg⟩
   rw [NLH_TermPartsFactor.source]
   unfold NLH_TermPartsFactor.reference
   rw [comp]
   unfold NLH_TermCompositionSource.validated validated
   cases result : validate_transition pub with
   | fail e=>rfl
   | div=>rfl
   | ok value=>
     cases value with
     | Err error=>rfl
     | Ok unit=>
       simpa only [bind_tc_ok] using tail
#print source
#print axioms source
end AspisR1.NLH_TermPartsSource
end
