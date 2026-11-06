import NJL_OccupancyHead
import NJL_WriteFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_OccupancyLanes
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_OccupancyContext (Context Domain)
open NJL_OccupancyHead (State)
def slot (lane : Fin 8) : Fin 12 := ⟨3+lane.val,by omega⟩
def inputSlot (lane : Fin 8) : Fin 16 := ⟨2+lane.val,by omega⟩
def reference (c : Context) (opened : Fin 16 → NQ) (before : State) (lane : Fin 8) : Result State := do
 let reply ← FIq_Native.field.PreparedQm31Multiplier.mul c.empty (opened (inputSlot lane))
 ok (NJB_StateUpdates.set before (slot lane) reply)
/-- NJB_K088/K089 arbitrary-prestate lane window, full12-cell frame. -/
def Cut (c : Context) (opened : Fin 16 → NQ) (before after : State) (lane : Fin 8)
 (reply right : NQ) (cache : FIv_PreparedNew.NP) (kind calls : Nat) : Prop :=
 calls=1 ∧ kind=4 ∧ cache=c.empty ∧ right=opened (inputSlot lane) ∧
 ∀ i,after i=if i.val=3+lane.val then reply else before i
def Step (c : Context) (opened : Fin 16 → NQ) (before after : State) (lane : Fin 8) : Prop :=
 ∃ reply,FIq_Native.field.PreparedQm31Multiplier.mul c.empty (opened (inputSlot lane))=ok reply ∧
 Cut c opened before after lane reply (opened (inputSlot lane)) c.empty 4 1
def modelStep (c : Context) (opened : Fin 16 → NQ) (lane : Fin 8) (before : Fin 12 → K) : Fin 12 → K :=
 NJL_WriteFrame.write before (slot lane) (decode c.emptyValue*decode (opened (inputSlot lane)))
theorem step (c : Context) (opened : Fin 16 → NQ) (before : State) (lane : Fin 8)
 (hc : Domain c) (ho : ∀ i,Canon (opened i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,reference c opened before lane=ok after ∧ Step c opened before after lane ∧
 (∀ i,Canon (after i)) ∧ (fun i=>decode (after i))=modelStep c opened lane (fun i=>decode (before i)) := by
 obtain ⟨reply,call,hr,value⟩ := NJB_PreparedLaws.mul_result c.empty c.emptyValue (opened (inputSlot lane))
  hc.2.2.2.1 (ho _) hc.2.2.2.2
 let after := NJB_StateUpdates.set before (slot lane) reply
 refine ⟨after,?_,⟨reply,call,rfl,rfl,rfl,rfl,?_⟩,?_,?_⟩
 · simp only [reference,call,bind_tc_ok];rfl
 · intro i
   have eq : slot lane=i ↔ i.val=3+lane.val := by simp only [Fin.ext_iff,slot];omega
   simp only [after,NJB_StateUpdates.set,eq]
 · intro i
   dsimp only [after,NJB_StateUpdates.set]
   split <;> first | exact hr | exact hb i
 · funext i
   by_cases same : slot lane=i
   · simp [after,NJB_StateUpdates.set,modelStep,NJL_WriteFrame.write,same,value]
   · simp [after,NJB_StateUpdates.set,modelStep,NJL_WriteFrame.write,same]
inductive Trace (c : Context) (opened : Fin 16 → NQ) : List (Fin 8) → State → State → Prop
 | nil (s) : Trace c opened [] s s
 | cons {i is before next last} : Step c opened before next i → Trace c opened is next last → Trace c opened (i::is) before last
def run (c : Context) (opened : Fin 16 → NQ) := NJB_StateUpdates.run (fun i before=>reference c opened before i)
theorem source (c : Context) (opened : Fin 16 → NQ) (xs : List (Fin 8)) (before : State)
 (hc : Domain c) (ho : ∀ i,Canon (opened i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,run c opened xs before=ok after ∧ Trace c opened xs before after ∧
 (∀ i,Canon (after i)) ∧ (fun i=>decode (after i))=xs.foldl (fun s i=>modelStep c opened i s) (fun i=>decode (before i)) := by
 induction xs generalizing before with
 | nil => exact ⟨before,rfl,.nil _,hb,rfl⟩
 | cons i is ih =>
  obtain ⟨next,call,cut,hn,value⟩ := step c opened before i hc ho hb
  obtain ⟨last,rest,trace,hl,vl⟩ := ih next hn
  refine ⟨last,?_,.cons cut trace,hl,?_⟩
  · simp only [run,NJB_StateUpdates.run,call,bind_tc_ok] at rest ⊢
    exact rest
  · simpa only [List.foldl_cons,value] using vl
#print axioms step
#print axioms source
end AspisR1.NJL_OccupancyLanes
end
