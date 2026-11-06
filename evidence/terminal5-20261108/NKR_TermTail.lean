import NHG_ExtraLeaves
import NJB_StubLaws
import NKI_AppendCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermTail
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIw_ArrayValue (canonical)
abbrev Carrier := NQ × Array NQ 16#usize × Array NQ 10#usize × NQ × NQ × NQ
abbrev Output := NQ × Array NQ 16#usize × Array NQ 10#usize × NQ
abbrev Error := pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1

def arithmetic (zc point : Array NQ 10#usize) (mu comp h active : NQ) : Result NQ := do
 let eq←pool_v1.pair_forest_semantic_terminal.equality_value zc point
 let weighted←field.QM31.mul eq comp
 let muH←field.QM31.mul mu h
 let sum←field.QM31.add weighted muH
 let mu2←field.QM31.mul mu mu
 let inactive←field.QM31.sub field.QM31.ONE active
 let inactiveH←field.QM31.mul inactive h
 let extra←field.QM31.mul mu2 inactiveH
 field.QM31.add sum extra

structure Calls (zc point : Array NQ 10#usize) (mu comp h active : NQ) where
 eq : NQ
 weighted : NQ
 muH : NQ
 sum : NQ
 mu2 : NQ
 inactive : NQ
 inactiveH : NQ
 extra : NQ
 out : NQ
 equality : pool_v1.pair_forest_semantic_terminal.equality_value zc point=ok eq
 weight : field.QM31.mul eq comp=ok weighted
 mu_h : field.QM31.mul mu h=ok muH
 sum_call : field.QM31.add weighted muH=ok sum
 mu_square : field.QM31.mul mu mu=ok mu2
 inactive_call : field.QM31.sub field.QM31.ONE active=ok inactive
 inactive_h : field.QM31.mul inactive h=ok inactiveH
 extra_call : field.QM31.mul mu2 inactiveH=ok extra
 returned : field.QM31.add sum extra=ok out

/-- The complete263 arithmetic suffix. CLOSED240 is consumed at SAME zc/point;
all eight field children and every canonical domain are internally derived.
This is support pending the parent237 packet and native suffix certificate. -/
theorem result (zc point : Array NQ 10#usize) (mu comp h active : NQ)
 (hz : canonical zc) (hp : canonical point) (hm : Canon mu)
 (hc : Canon comp) (hh : Canon h) (ha : Canon active) :
 ∃ c : Calls zc point mu comp h active,
 arithmetic zc point mu comp h active=ok c.out ∧ Canon c.out ∧
 decode c.out=FIv_EqualityValue.weight zc point*decode comp+decode mu*decode h+
  decode mu^2*((1-decode active)*decode h) := by
 obtain ⟨eq,ce,he,ve⟩ := NHG_ExtraLeaves.equality_result zc point hz hp
 obtain ⟨weighted,cw,hw,vw⟩ := NJB_StubLaws.qm_mul eq comp he hc
 obtain ⟨muH,cmh,hmh,vmh⟩ := NJB_StubLaws.qm_mul mu h hm hh
 obtain ⟨sum,cs,hs,vs⟩ := NJB_StubLaws.qm_add weighted muH hw hmh
 obtain ⟨mu2,cm2,hm2,vm2⟩ := NJB_StubLaws.qm_mul mu mu hm hm
 obtain ⟨inactive,ci,hi,vi⟩ := NJB_StubLaws.qm_sub field.QM31.ONE active FIv_NativeValue.one.1 ha
 obtain ⟨inactiveH,cih,hih,vih⟩ := NJB_StubLaws.qm_mul inactive h hi hh
 obtain ⟨extra,cx,hx,vx⟩ := NJB_StubLaws.qm_mul mu2 inactiveH hm2 hih
 obtain ⟨out,co,ho,vo⟩ := NJB_StubLaws.qm_add sum extra hs hx
 let c : Calls zc point mu comp h active := ⟨eq,weighted,muH,sum,mu2,inactive,inactiveH,extra,out,ce,cw,cmh,cs,cm2,ci,cih,cx,co⟩
 refine ⟨c,?_,ho,?_⟩
 · simp only [arithmetic,ce,cw,cmh,cs,cm2,ci,cih,cx,co,bind_tc_ok]
 · change decode out=_
   rw [vo,vs,vw,vmh,vx,vm2,vih,vi,ve,FIv_NativeValue.one.2]
   ring

/-- Full terminal suffix, preserving the child237 returned c1/mask/g channels. -/
def tail (zc point : Array NQ 10#usize) (mu : NQ) (child : Carrier) : Result Output := do
 let original←arithmetic zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2
 ok (original,child.2.1,child.2.2.1,child.2.2.2.1)

/-- Every actual inner Result arm is propagated; the field suffix is entered
only for Ok, while Aeneas fail/div are propagated by its native bind. -/
def after (zc point : Array NQ 10#usize) (mu : NQ) : core.result.Result Carrier Error → Result (core.result.Result Output Error)
 | .Err e => ok (.Err e)
 | .Ok child => do let output←tail zc point mu child;ok (.Ok output)

#print axioms result
end AspisR1.NKR_TermTail
end
