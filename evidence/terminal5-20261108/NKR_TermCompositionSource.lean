import NKR_TermCompositionFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermCompositionSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal

def validated (pub : Public) (out : NKR_TermTail.Carrier) := do
 let result←validate_transition pub
 match result with
 | .Err error=>ok (.Err error)
 | .Ok _=>ok (.Ok out)

/-- Whole237 emitted source on arbitrary public amounts. Its own precheck
establishes the261 amount domain; every validation Err/fail/div preserves the
prefix and never enters the continuation. This is source SUPPORT until the
native237 cuts and native218/261 children have composed. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (hd : NKR_DigestChildren.Domain pub)
 (hc : canonical claims) (hp : canonical point) (hl : Canon lambda)
 (hchi : Canon chi) (ht : Canon theta) (asset : pub.asset_id.val<2147483647) :
 (NKR_TermAmount.invalid pub.withdrawal_amount=true ∧
  composition_parts pub claims point lambda chi theta=ok (.Err .InvalidPublicAmount)) ∨
 ∃ out : NKR_TermTail.Carrier,NKR_TermAmount.invalid pub.withdrawal_amount=false ∧
  composition_parts pub claims point lambda chi theta=validated pub out ∧
  Canon out.1 ∧ Canon out.2.2.2.1 ∧ Canon out.2.2.2.2.1 ∧ Canon out.2.2.2.2.2 ∧
  canonical out.2.1 ∧ canonical out.2.2.1 := by
 cases bad : NKR_TermAmount.invalid pub.withdrawal_amount with
 | true=>exact Or.inl ⟨bad,NKR_TermAmount.rejected pub claims point lambda chi theta bad⟩
 | false=>
   have amount:=NKR_TermAmount.canonical pub bad
   obtain ⟨out,tail,cc,cg,ch,ca,cz,cm⟩:=NKR_TermComposeTail.source pub claims point lambda chi theta hd hc hp hl hchi ht asset amount
   refine Or.inr ⟨out,bad,?_,cc,cg,ch,ca,cz,cm⟩
   rw [NKR_TermCompositionFactor.source]
   unfold NKR_TermCompositionFactor.reference validated
   rw [NKR_TermAmount.source,bind_tc_ok]
   simp only [Aeneas.Std.uncurry,bad,Bool.false_eq_true,ite_false]
   cases result : validate_transition pub with
   | fail e=>rfl
   | div=>rfl
   | ok value=>cases value <;> simp only [bind_tc_ok,tail]
#print source
#print axioms source
end AspisR1.NKR_TermCompositionSource
end
