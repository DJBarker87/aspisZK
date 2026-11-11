import NKR_SumFinishPattern
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumPatternTrace
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NKR_SumFinishData
open NKR_SumFinishPattern (Scratch State scratchIndex)

/-- NKR_pattern_step_cut in NKR_SumPattern_native.rs.txt: exact mul/add
arguments and ordering,two calls,coordinate+1,and complete26-cell frame.
Opaque field replies are unconstrained here; their full emitted Results
are the separate internally-discharged Invocation clauses. -/
def Cut (scratch : Scratch) (lows : Fin 16 → NQ) (c : Fin 43) (before after : State)
 (product reply : NQ) (left right : Fin 2 → NQ) (kinds : Fin 2 → Nat) (calls next : Nat) : Prop :=
 calls=2 ∧ kinds=![0,1] ∧ next=c.val+1 ∧
 left 0=scratch (scratchIndex c) ∧ right 0=lows (pLow c) ∧
 left 1=before (pOut c) ∧ right 1=product ∧
 ∀ i,after i=if pOut c=i then reply else before i

def Invocation (scratch : Scratch) (lows : Fin 16 → NQ) (c : Fin 43) (before after : State) : Prop :=
 ∃ product reply,
 FIq_Native.field.QM31.mul (scratch (scratchIndex c)) (lows (pLow c))=ok product ∧
 FIq_Native.field.QM31.add (before (pOut c)) product=ok reply ∧
 Cut scratch lows c before after product reply
  ![scratch (scratchIndex c),before (pOut c)] ![lows (pLow c),product] ![0,1] 2 (c.val+1)

theorem step (scratch : Scratch) (lows : Fin 16 → NQ) (c : Fin 43) (before : State)
 (hs : ∀ i,Canon (scratch i)) (hl : ∀ i,Canon (lows i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NKR_SumFinishPattern.step scratch lows c before=ok after ∧
 Invocation scratch lows c before after ∧ ∀ i,Canon (after i) := by
 obtain ⟨product,mulCall,cp,_⟩ := NJB_StubLaws.qm_mul (scratch (scratchIndex c)) (lows (pLow c)) (hs _) (hl _)
 obtain ⟨reply,addCall,cr,_⟩ := NJB_StubLaws.qm_add (before (pOut c)) product (hb _) cp
 let after := NJB_StateUpdates.set before (pOut c) reply
 refine ⟨after,?_,⟨product,reply,mulCall,addCall,?_⟩,?_⟩
 · simp only [NKR_SumFinishPattern.step,NJB_StateUpdates.mulAdd,NJB_StateUpdates.add,mulCall,addCall,bind_tc_ok];rfl
 · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _=>rfl⟩
 · intro i
   dsimp only [after,NJB_StateUpdates.set]
   split <;> first | exact cr | exact hb i

inductive Trace (scratch : Scratch) (lows : Fin 16 → NQ) : List (Fin 43) → State → State → Prop
 | nil (s) : Trace scratch lows [] s s
 | cons {c cs before next after} : Invocation scratch lows c before next →
  Trace scratch lows cs next after → Trace scratch lows (c::cs) before after

theorem source (scratch : Scratch) (lows : Fin 16 → NQ) (cs : List (Fin 43)) (before : State)
 (hs : ∀ i,Canon (scratch i)) (hl : ∀ i,Canon (lows i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.run (NKR_SumFinishPattern.step scratch lows) cs before=ok after ∧
 Trace scratch lows cs before after ∧ ∀ i,Canon (after i) := by
 induction cs generalizing before with
 | nil => exact ⟨before,rfl,.nil before,hb⟩
 | cons c cs ih =>
  obtain ⟨next,hn,inv,cn⟩ := step scratch lows c before hs hl hb
  obtain ⟨after,ha,tr,ca⟩ := ih next cn
  exact ⟨after,by simp only [NJB_StateUpdates.run,hn,ha,bind_tc_ok],.cons inv tr,ca⟩

#print axioms step
#print axioms source
end AspisR1.NKR_SumPatternTrace
end
