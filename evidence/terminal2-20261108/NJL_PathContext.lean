import NJL_OccupancyContext
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PathContext
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIv_PreparedNew (NP)
abbrev State := Fin 17 → NQ
structure Context where
 selected : NQ
 emptyValue : NQ
 left : NP
 right : NP
 head : NQ
def initial (c : Context) : State := fun i=>if i.val=0 then c.head else FIq_Native.field.QM31.ZERO
def reference (selector bit : NQ) : Result Context := do
 let selected ← FIq_Native.field.QM31.mul selector bit
 let emptyValue ← FIq_Native.field.QM31.sub selector selected
 let left ← FIq_Native.field.PreparedQm31Multiplier.new emptyValue
 let right ← FIq_Native.field.PreparedQm31Multiplier.new selected
 let residual ← FIq_Native.field.QM31.sub bit FIq_Native.field.QM31.ONE
 let head ← FIq_Native.field.QM31.mul selected residual
 ok ⟨selected,emptyValue,left,right,head⟩
def Domain (c : Context) : Prop :=
 Canon c.selected ∧ Canon c.emptyValue ∧ Canon c.head ∧
 NJB_PreparedLaws.Domain c.left c.emptyValue ∧ NJB_PreparedLaws.Domain c.right c.selected
def Clauses (selector bit residual : NQ) (c : Context) : Prop :=
 FIq_Native.field.QM31.mul selector bit=ok c.selected ∧
 FIq_Native.field.QM31.sub selector c.selected=ok c.emptyValue ∧
 FIq_Native.field.PreparedQm31Multiplier.new c.emptyValue=ok c.left ∧
 FIq_Native.field.PreparedQm31Multiplier.new c.selected=ok c.right ∧
 FIq_Native.field.QM31.sub bit FIq_Native.field.QM31.ONE=ok residual ∧
 FIq_Native.field.QM31.mul c.selected residual=ok c.head
/-- NJB_path_head_proof: exact six kinds/inputs, two actual9-word caches,
right operands only at non-constructor events, and all17 output cells. -/
def Cut (selector bit residual : NQ) (c : Context) (events : Fin 6 → NJB_Cuts.Event)
 (leftSeen rightSeen : NP) (out : State) (calls news : Nat) : Prop :=
 calls=6 ∧ news=2 ∧ leftSeen=c.left ∧ rightSeen=c.right ∧
 (∀ j,(events j).operation=(![0,2,3,3,2,0] : Fin 6 → Nat) j ∧
  (events j).left=(![selector,selector,c.emptyValue,c.selected,bit,c.selected] : Fin 6 → NQ) j) ∧
 (events 0).right=bit ∧ (events 1).right=c.selected ∧
 (events 4).right=FIq_Native.field.QM31.ONE ∧ (events 5).right=residual ∧
 ∀ i,out i=if i.val=0 then c.head else FIq_Native.field.QM31.ZERO
theorem source (selector bit : NQ) (hs : Canon selector) (hb : Canon bit) :
 ∃ c residual events,reference selector bit=ok c ∧ Domain c ∧ Clauses selector bit residual c ∧
 Cut selector bit residual c events c.left c.right (initial c) 6 2 ∧
 (∀ i,Canon (initial c i)) ∧
 decode c.selected=decode selector*decode bit ∧
 decode c.emptyValue=decode selector*(1-decode bit) ∧
 decode c.head=decode selector*(decode bit*(decode bit-1)) := by
 obtain ⟨s,h0,c0,v0⟩ := NJB_StubLaws.qm_mul selector bit hs hb
 obtain ⟨e,h1,c1,v1⟩ := NJB_StubLaws.qm_sub selector s hs c0
 obtain ⟨l,h2,d2⟩ := NJB_PreparedLaws.new_result e c1
 obtain ⟨r,h3,d3⟩ := NJB_PreparedLaws.new_result s c0
 obtain ⟨b,h4,c4,v4⟩ := NJB_StubLaws.qm_sub bit FIq_Native.field.QM31.ONE hb FIv_NativeValue.one.1
 obtain ⟨h,h5,c5,v5⟩ := NJB_StubLaws.qm_mul s b c0 c4
 let c : Context := ⟨s,e,l,r,h⟩
 let events : Fin 6 → NJB_Cuts.Event := fun j=>
  ⟨(![0,2,3,3,2,0] : Fin 6 → Nat) j,
   (![selector,selector,e,s,bit,s] : Fin 6 → NQ) j,
   (![bit,s,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ONE,b] : Fin 6 → NQ) j⟩
 refine ⟨c,b,events,?_,⟨c0,c1,c5,d2,d3⟩,⟨h0,h1,h2,h3,h4,h5⟩,?_,?_,v0,?_,?_⟩
 · simp only [reference,h0,h1,h2,h3,h4,h5,bind_tc_ok];rfl
 · exact ⟨rfl,rfl,rfl,rfl,by intro j;fin_cases j <;> exact ⟨rfl,rfl⟩,rfl,rfl,rfl,rfl,fun _=>rfl⟩
 · intro i
   dsimp only [initial]
   split <;> first | exact c5 | exact FIv_NativeValue.zero.1
 · change decode e=decode selector*(1-decode bit)
   rw [v1,v0];ring
 · change decode h=decode selector*(decode bit*(decode bit-1))
   rw [v5,v0,v4,FIv_NativeValue.one.2];ring
#print source
#print axioms source
end AspisR1.NJL_PathContext
end
