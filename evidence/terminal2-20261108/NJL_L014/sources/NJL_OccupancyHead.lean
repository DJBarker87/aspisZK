import NJL_OccupancyContext
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_OccupancyHead
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_OccupancyContext (Context Domain)
abbrev State := Fin 12 → NQ
def state (r : Fin 6 → NQ) : State := fun i=>
 if i.val=0 then r 1 else if i.val=1 then r 4 else if i.val=2 then r 5 else FIq_Native.field.QM31.ZERO
def reference (c : Context) (occupied inverse nine : NQ) : Result State := do
 let r0 ← FIq_Native.field.QM31.sub occupied FIq_Native.field.QM31.ONE
 let r1 ← FIq_Native.field.QM31.mul c.selected r0
 let r2 ← FIq_Native.field.QM31.mul nine inverse
 let r3 ← FIq_Native.field.QM31.sub r2 occupied
 let r4 ← FIq_Native.field.QM31.mul c.both r3
 let r5 ← FIq_Native.field.PreparedQm31Multiplier.mul c.empty inverse
 ok (state ![r0,r1,r2,r3,r4,r5])
def Clauses (c : Context) (occupied inverse nine : NQ) (r : Fin 6 → NQ) : Prop :=
 FIq_Native.field.QM31.sub occupied FIq_Native.field.QM31.ONE=ok (r 0) ∧
 FIq_Native.field.QM31.mul c.selected (r 0)=ok (r 1) ∧
 FIq_Native.field.QM31.mul nine inverse=ok (r 2) ∧
 FIq_Native.field.QM31.sub (r 2) occupied=ok (r 3) ∧
 FIq_Native.field.QM31.mul c.both (r 3)=ok (r 4) ∧
 FIq_Native.field.PreparedQm31Multiplier.mul c.empty inverse=ok (r 5)
/-- Exact NJB_K086/K087 head assertion: all12 output cells including zero
frame, six operation kinds/operands and the actual prepared cache at slot5. -/
def Cut (c : Context) (occupied inverse nine : NQ) (r : Fin 6 → NQ)
 (events : Fin 6 → NJB_Cuts.Event) (cache : FIv_PreparedNew.NP) (calls : Nat) (out : State) : Prop :=
 calls=6 ∧ cache=c.empty ∧
 (∀ j,(events j).operation=(![2,0,0,2,0,4] : Fin 6 → Nat) j ∧
 (events j).right=(![FIq_Native.field.QM31.ONE,r 0,inverse,occupied,r 3,inverse] : Fin 6 → NQ) j) ∧
 (∀ j : Fin 5,(events j.castSucc).left=(![occupied,c.selected,nine,r 2,c.both] : Fin 5 → NQ) j) ∧
 ∀ i,out i=state r i
def model (c : Context) (occupied inverse nine : NQ) : Fin 12 → K := fun i=>
 if i.val=0 then decode c.selected*(decode occupied-1)
 else if i.val=1 then decode c.both*(decode nine*decode inverse-decode occupied)
 else if i.val=2 then decode c.emptyValue*decode inverse else 0
theorem source (c : Context) (occupied inverse nine : NQ) (hc : Domain c)
 (ho : Canon occupied) (hi : Canon inverse) (hn : Canon nine) :
 ∃ r out events, reference c occupied inverse nine=ok out ∧
 Clauses c occupied inverse nine r ∧ Cut c occupied inverse nine r events c.empty 6 out ∧
 (∀ i,Canon (out i)) ∧ (fun i=>decode (out i))=model c occupied inverse nine := by
 obtain ⟨r0,h0,c0,v0⟩ := NJB_StubLaws.qm_sub occupied FIq_Native.field.QM31.ONE ho FIv_NativeValue.one.1
 obtain ⟨r1,h1,c1,v1⟩ := NJB_StubLaws.qm_mul c.selected r0 hc.2.2.1 c0
 obtain ⟨r2,h2,c2,v2⟩ := NJB_StubLaws.qm_mul nine inverse hn hi
 obtain ⟨r3,h3,c3,v3⟩ := NJB_StubLaws.qm_sub r2 occupied c2 ho
 obtain ⟨r4,h4,c4,v4⟩ := NJB_StubLaws.qm_mul c.both r3 hc.2.1 c3
 obtain ⟨r5,h5,c5,v5⟩ := NJB_PreparedLaws.mul_result c.empty c.emptyValue inverse hc.2.2.2.1 hi hc.2.2.2.2
 let r : Fin 6 → NQ := ![r0,r1,r2,r3,r4,r5]
 let events : Fin 6 → NJB_Cuts.Event := fun j=>
  ⟨(![2,0,0,2,0,4] : Fin 6 → Nat) j,
   (![occupied,c.selected,nine,r2,c.both,FIq_Native.field.QM31.ZERO] : Fin 6 → NQ) j,
   (![FIq_Native.field.QM31.ONE,r0,inverse,occupied,r3,inverse] : Fin 6 → NQ) j⟩
 refine ⟨r,state r,events,?_,⟨h0,h1,h2,h3,h4,h5⟩,?_,?_,?_⟩
 · simp only [reference,h0,h1,h2,h3,h4,h5,bind_tc_ok];rfl
 · refine ⟨rfl,rfl,?_,?_,fun _=>rfl⟩
   · intro j;fin_cases j <;> exact ⟨rfl,rfl⟩
   · intro j;fin_cases j <;> rfl
 · intro i
   dsimp only [state]
   split <;> first | exact c1 | (split <;> first | exact c4 | (split <;> first | exact c5 | exact FIv_NativeValue.zero.1))
 · funext i
   by_cases h0' : i.val=0
   · simp [state,model,h0',r,v1,v0,FIv_NativeValue.one.2]
   · by_cases h1' : i.val=1
     · simp [state,model,h0',h1',r,v4,v3,v2]
     · by_cases h2' : i.val=2
       · simp [state,model,h0',h1',h2',r,v5]
       · simp [state,model,h0',h1',h2',FIv_NativeValue.zero.2]
#print source
#print axioms source
end AspisR1.NJL_OccupancyHead
end
