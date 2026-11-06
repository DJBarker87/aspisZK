import NKR_TermTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermCut
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open NKR_TermTail (Calls Carrier Output)
open NKI_AppendCut (Event)
def kinds : Fin 9 → Nat := ![0,1,1,2,1,3,1,1,2]
def left {zc point mu comp h active} (c : Calls zc point mu comp h active) : Fin 9 → NQ :=
 ![field.QM31.ZERO,c.eq,mu,c.weighted,mu,field.QM31.ONE,c.inactive,c.mu2,c.sum]
def right {zc point mu comp h active} (c : Calls zc point mu comp h active) : Fin 9 → NQ :=
 ![field.QM31.ZERO,comp,h,c.muH,mu,active,h,c.inactiveH,c.extra]
structure Observation where
 equalityLeft : Array NQ 10#usize
 equalityRight : Array NQ 10#usize
 events : Fin 9 → Event
 result : Output
 calls : Nat
/-- NKR_terminal_suffix_cut exact asserted operand/event/return projections.
Read-only input arrays and complete unchanged child c1/mask/g channels are
retained; only the declared scalar reply is newly returned. -/
def Cut (zc point : Array NQ 10#usize) (mu : NQ) (child : Carrier)
 (c : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2)
 (ob : Observation) : Prop :=
 ob.equalityLeft=zc ∧ ob.equalityRight=point ∧ ob.calls=9 ∧
 (∀ i,(ob.events i).kind=kinds i ∧ (ob.events i).left=left c i ∧ (ob.events i).right=right c i) ∧
 ob.result=(c.out,child.2.1,child.2.2.1,child.2.2.2.1)
def observations (zc point : Array NQ 10#usize) (mu : NQ) (child : Carrier)
 (c : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2) : Observation :=
 ⟨zc,point,(fun i=>⟨kinds i,left c i,right c i⟩),(c.out,child.2.1,child.2.2.1,child.2.2.2.1),9⟩

theorem source (zc point : Array NQ 10#usize) (mu : NQ) (child : Carrier)
 (hz : canonical zc) (hp : canonical point) (hm : Canon mu)
 (hc : Canon child.1) (hh : Canon child.2.2.2.2.1) (ha : Canon child.2.2.2.2.2) :
 ∃ c : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2,
 NKR_TermTail.after zc point mu (.Ok child)=ok (.Ok (observations zc point mu child c).result) ∧
 Cut zc point mu child c (observations zc point mu child c) ∧ Canon c.out := by
 obtain ⟨c,call,co,_⟩:=NKR_TermTail.result zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2 hz hp hm hc hh ha
 refine ⟨c,?_,⟨rfl,rfl,rfl,fun _=>⟨rfl,rfl,rfl⟩,rfl⟩,co⟩
 simp only [NKR_TermTail.after,NKR_TermTail.tail,call,bind_tc_ok]
 rfl

/-- NKR_terminal_error_prefix_cut: both source errors retain identity and
enter no field/equality suffix event. This is a complete Result arm. -/
theorem error_prefix (zc point : Array NQ 10#usize) (mu : NQ) (error : NKR_TermTail.Error) :
 NKR_TermTail.after zc point mu (.Err error)=ok (.Err error) := rfl
#print axioms source
#print axioms error_prefix
end AspisR1.NKR_TermCut
end
