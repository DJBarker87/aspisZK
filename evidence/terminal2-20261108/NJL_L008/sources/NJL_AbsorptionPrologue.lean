import NJB_AbsorptionCuts
import NJB_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_AbsorptionPrologue
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
def left (a : Fin 5 → NQ) (r : Fin 7 → NQ) : Fin 7 → NQ :=
 ![a 0,a 1,a 0,a 1,r 3,r 4,a 0]
def right (a : Fin 5 → NQ) (r : Fin 7 → NQ) : Fin 7 → NQ :=
 ![a 1,a 2,r 1,a 2,a 3,a 4,r 5]
def kind : Fin 7 → Nat := ![0,1,0,1,1,1,0]
def replyIndex : Fin 3 → Fin 7 := ![0,2,6]
def positions : Fin 3 → Nat := ![1,3,7]
/-- K040/K041 NJB_absorption_scales assertion transcription, actual 9-word
caches. Arithmetic count7, new count3, new positions1/3/7, exact argument and
cache identity. No interpretation of the arbitrary prepared reply is assumed.
Pinned source: NJB_absorption.rs.txt, see NJL_CUTS.md. -/
def Cut (a : Fin 5 → NQ) (r : Fin 7 → NQ) (p : Fin 3 → NP)
 (events : Fin 7 → NJB_Cuts.Event) (newArgs : Fin 3 → NQ)
 (newAt : Fin 3 → Nat) (seen out : Fin 3 → NP) (calls news : Nat) : Prop :=
 (∀ i,Canon (a i)) ∧ (∀ i,Canon (r i)) ∧ calls=7 ∧ news=3 ∧
 (∀ j,(events j).operation=kind j ∧ (events j).left=left a r j ∧ (events j).right=right a r j) ∧
 (∀ j,newArgs j=r (replyIndex j) ∧ newAt j=positions j ∧ seen j=p j ∧ out j=p j)
def Clauses (a : Fin 5 → NQ) (r : Fin 7 → NQ) (p : Fin 3 → NP) : Prop :=
 (∀ j,(if kind j=0 then FIq_Native.field.QM31.mul (left a r j) (right a r j)
  else FIq_Native.field.QM31.add (left a r j) (right a r j))=ok (r j)) ∧
 (∀ j,FIq_Native.field.PreparedQm31Multiplier.new (r (replyIndex j))=ok (p j))
/-- All actual child calls, cache domains and repeated additions in SOURCE
order, discharging the prologue cut without a child success hypothesis. -/
theorem source (low fixed two eight nodes : NQ)
 (hl : Canon low) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes) :
 ∃ r p scales,
 Cut ![low,fixed,two,eight,nodes] r p
  (fun j=>⟨kind j,left ![low,fixed,two,eight,nodes] r j,right ![low,fixed,two,eight,nodes] r j⟩)
  (fun j=>r (replyIndex j)) positions p p 7 3 ∧
 Clauses ![low,fixed,two,eight,nodes] r p ∧
 NJB_AbsorptionScales.reference low fixed two eight nodes=ok scales ∧
 (∀ j,(scales j).value=r (replyIndex j) ∧ (scales j).cache=p j ∧
  Canon (scales j).value ∧ NJB_PreparedLaws.Domain (scales j).cache (scales j).value) := by
 obtain ⟨q0,h0,c0,_⟩ := NJB_StubLaws.qm_mul low fixed hl hf
 obtain ⟨p0,n0,d0⟩ := NJB_PreparedLaws.new_result q0 c0
 obtain ⟨t1,a1,ct1,_⟩ := NJB_StubLaws.qm_add fixed two hf ht
 obtain ⟨q1,h1,c1,_⟩ := NJB_StubLaws.qm_mul low t1 hl ct1
 obtain ⟨p1,n1,d1⟩ := NJB_PreparedLaws.new_result q1 c1
 obtain ⟨t2,a2,ct2,_⟩ := NJB_StubLaws.qm_add fixed two hf ht
 obtain ⟨t3,a3,ct3,_⟩ := NJB_StubLaws.qm_add t2 eight ct2 he
 obtain ⟨t4,a4,ct4,_⟩ := NJB_StubLaws.qm_add t3 nodes ct3 hn
 obtain ⟨q2,h2,c2,_⟩ := NJB_StubLaws.qm_mul low t4 hl ct4
 obtain ⟨p2,n2,d2⟩ := NJB_PreparedLaws.new_result q2 c2
 let r : Fin 7 → NQ := ![q0,t1,q1,t2,t3,t4,q2]
 let p : Fin 3 → NP := ![p0,p1,p2]
 let scales : Fin 3 → NJB_AbsorptionScales.Scale := ![⟨q0,p0⟩,⟨q1,p1⟩,⟨q2,p2⟩]
 refine ⟨r,p,scales,?_,?_,?_,?_⟩
 · refine ⟨?_,?_,rfl,rfl,fun _=>⟨rfl,rfl,rfl⟩,fun _=>⟨rfl,rfl,rfl,rfl⟩⟩
   · intro j;fin_cases j <;> assumption
   · intro j;fin_cases j <;> first | exact c0 | exact ct1 | exact c1 | exact ct2 | exact ct3 | exact ct4 | exact c2
 · constructor
   · intro j;fin_cases j
     · exact h0
     · exact a1
     · exact h1
     · exact a2
     · exact a3
     · exact a4
     · exact h2
   · intro j;fin_cases j
     · exact n0
     · exact n1
     · exact n2
 · simp only [NJB_AbsorptionScales.reference,h0,n0,a1,h1,n1,a2,a3,a4,h2,n2,bind_tc_ok]
   rfl
 · intro j;fin_cases j
   · exact ⟨rfl,rfl,c0,d0⟩
   · exact ⟨rfl,rfl,c1,d1⟩
   · exact ⟨rfl,rfl,c2,d2⟩
#print source
#print axioms source
end AspisR1.NJL_AbsorptionPrologue
end
