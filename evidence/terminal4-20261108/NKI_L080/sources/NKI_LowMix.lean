import NJB_PreparedLaws
import NKI_AppendCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LowMix
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (NP)
abbrev State := Fin 2 → NQ
def reference (before : State) (low : NQ) (sums : State) : Result State := do
 let p←FIq_Native.field.PreparedQm31Multiplier.new low
 let a←FIq_Native.field.PreparedQm31Multiplier.mul p (sums 0)
 let x←FIq_Native.field.QM31.add (before 0) a
 let b←FIq_Native.field.PreparedQm31Multiplier.mul p (sums 1)
 let y←FIq_Native.field.QM31.add (before 1) b
 ok ![x,y]
structure Packet (before : State) (low : NQ) (sums : State) where
 cache : NP
 product : State
 out : State
 constructor : FIq_Native.field.PreparedQm31Multiplier.new low=ok cache
 domain : NJB_PreparedLaws.Domain cache low
 products : ∀ g,FIq_Native.field.PreparedQm31Multiplier.mul cache (sums g)=ok (product g)
 additions : ∀ g,FIq_Native.field.QM31.add (before g) (product g)=ok (out g)
 canonical : ∀ g,Canon (out g)
 values : ∀ g,decode (out g)=decode (before g)+decode low*decode (sums g)
/-- K011/012 actual251low0/11/12five-call window. Source actual constructor,
all9cache words, operands, order and complete2cell output. SUPPORT only until
full251public-digest/old-cohort association is established. -/
def Cut (before : State) (low : NQ) (sums : State) (p : NP) (product reply out : State)
 (events : Fin 5 → NKI_AppendCut.Event)
 (seenCache : Fin 2 → NJB_PreparedCarrier.Index → NJB_PreparedCarrier.Index → U32) (calls : Nat) : Prop :=
 calls=5 ∧ (events 0).kind=3 ∧ (events 0).left=low ∧
 (∀ g : Fin 2,(events ⟨1+2*g.val,by have h:=g.isLt;omega⟩).kind=4 ∧
  (events ⟨1+2*g.val,by have h:=g.isLt;omega⟩).right=sums g ∧ seenCache g=NJB_PreparedCarrier.words p ∧
  (events ⟨2+2*g.val,by have h:=g.isLt;omega⟩).kind=1 ∧
  (events ⟨2+2*g.val,by have h:=g.isLt;omega⟩).left=before g ∧
  (events ⟨2+2*g.val,by have h:=g.isLt;omega⟩).right=product g ∧ out g=reply g)
def events (before : State) (low : NQ) (sums product : State) : Fin 5 → NKI_AppendCut.Event :=
 ![⟨3,low,FIq_Native.field.QM31.ZERO⟩,⟨4,FIq_Native.field.QM31.ZERO,sums 0⟩,⟨1,before 0,product 0⟩,
   ⟨4,FIq_Native.field.QM31.ZERO,sums 1⟩,⟨1,before 1,product 1⟩]
theorem source (before : State) (low : NQ) (sums : State)
 (hb : ∀ g,Canon (before g)) (hl : Canon low) (hs : ∀ g,Canon (sums g)) :
 ∃ p : Packet before low sums,reference before low sums=ok p.out ∧
 Cut before low sums p.cache p.product p.out p.out (events before low sums p.product) (fun _=>NJB_PreparedCarrier.words p.cache) 5 := by
 obtain ⟨cache,cc,dc⟩ := NJB_PreparedLaws.new_result low hl
 choose product cp hp vp using (fun g : Fin 2=>NJB_PreparedLaws.mul_result cache low (sums g) hl (hs g) dc)
 choose out co ho vo using (fun g : Fin 2=>NJB_StubLaws.qm_add (before g) (product g) (hb g) (hp g))
 let p : Packet before low sums:=⟨cache,product,out,cc,dc,cp,co,ho,fun g=>by rw [vo,vp]⟩
 refine ⟨p,?_,rfl,rfl,rfl,?_⟩
 · have vector : (![out 0,out 1] : State)=out := by funext g;fin_cases g <;> rfl
   simp only [reference,cc,cp,co,bind_tc_ok,vector]
 · intro g
   fin_cases g <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print source
#print axioms source
end AspisR1.NKI_LowMix
end
