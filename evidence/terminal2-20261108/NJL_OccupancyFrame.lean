import NJL_OccupancyLanes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_OccupancyFrame
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode K)
open FIv_NativeArithmetic (NQ)
open NJL_OccupancyContext (Context Domain)
open NJL_OccupancyHead (State)
open NJL_OccupancyLanes (slot inputSlot modelStep)
def indices : List (Fin 8) := List.ofFn (fun i : Fin 8=>i)
def sourceIndex (i : Fin 12) : Fin 16 := ⟨i.val-1,by omega⟩
def value (c : Context) (opened : Fin 16 → NQ) (i : Fin 12) : K :=
 decode c.emptyValue*decode (opened (sourceIndex i))
theorem input_same (lane : Fin 8) : sourceIndex (slot lane)=inputSlot lane := by
 apply Fin.ext
 dsimp only [sourceIndex,slot,inputSlot]
 omega
theorem model_step (c : Context) (opened : Fin 16 → NQ) (lane : Fin 8) (before : Fin 12 → K) :
 modelStep c opened lane before=NJL_WriteFrame.write before (slot lane) (value c opened (slot lane)) := by
 rw [value,input_same]
 rfl
theorem model_run (c : Context) (opened : Fin 16 → NQ) (xs : List (Fin 8)) (before : Fin 12 → K) :
 xs.foldl (fun s i=>modelStep c opened i s) before=
 (xs.map slot).foldl (fun s i=>NJL_WriteFrame.write s i (value c opened i)) before := by
 induction xs generalizing before with
 | nil => rfl
 | cons i is ih => simpa only [List.foldl_cons,List.map_cons,model_step] using ih (modelStep c opened i before)
theorem full_mem (i : Fin 12) : i∈indices.map slot ↔ (3 : Nat) ≤ i.val ∧ i.val < 11 := by
 constructor
 · intro member
   obtain ⟨lane,_,same⟩ := List.mem_map.mp member
   have hv := congrArg Fin.val same
   dsimp only [slot] at hv
   have := lane.isLt
   omega
 · intro bound
   let lane : Fin 8 := ⟨i.val-3,by omega⟩
   refine List.mem_map.mpr ⟨lane,?_,?_⟩
   · exact List.mem_ofFn.mpr ⟨lane,rfl⟩
   · apply Fin.ext
     dsimp only [slot,lane]
     omega
/-- All8 arbitrary native windows compose into an exact12-cell frame. No
unconstrained seed or address/payload principle is used. -/
theorem source (c : Context) (opened : Fin 16 → NQ) (before : State)
 (hc : Domain c) (ho : ∀ i,Canon (opened i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJL_OccupancyLanes.run c opened indices before=ok after ∧
 NJL_OccupancyLanes.Trace c opened indices before after ∧ (∀ i,Canon (after i)) ∧
 (∀ i,decode (after i)=if (3 : Nat) ≤ i.val ∧ i.val < 11 then value c opened i else decode (before i)) := by
 obtain ⟨after,call,trace,ha,va⟩ := NJL_OccupancyLanes.source c opened indices before hc ho hb
 refine ⟨after,call,trace,ha,?_⟩
 intro i
 have point := congrFun va i
 rw [model_run,NJL_WriteFrame.fold] at point
 simpa only [full_mem] using point
#print axioms input_same
#print axioms model_step
#print axioms model_run
#print axioms full_mem
#print axioms source
end AspisR1.NJL_OccupancyFrame
end
