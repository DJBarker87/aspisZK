import NJL_PathTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PathFrame
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_PathContext (Context Domain State)
open NJL_PathStep (weight sourceIndex currentIndex target)
open NJL_PathTrace (Job jobs)
def look (a : Fin 16 → NQ) (n : Nat) : K := if h : n<16 then decode (a ⟨n,h⟩) else 0
theorem look_fin (a : Fin 16 → NQ) (i : Fin 16) : look a i.val=decode (a i) := by simp [look,i.isLt]
def value (c : Context) (z succ : Fin 16 → NQ) (i : Fin 17) : K :=
 if (9 : Nat) ≤ i.val then decode c.selected*(look succ (i.val-1)-look z (i.val-8))
 else if (1 : Nat) ≤ i.val then decode c.emptyValue*(look succ (i.val-1)-look z i.val)
 else decode c.head
theorem target_value (c : Context) (z succ : Fin 16 → NQ) (right : Bool) (k : Fin 8) :
 value c z succ (target right k)=decode (weight c right)*(decode (succ (sourceIndex right k))-decode (z (currentIndex k))) := by
 cases right
 · have h9 : ¬(9 : Nat) ≤ (target false k).val := by dsimp [target];have := k.isLt;omega
   have h1 : (1 : Nat) ≤ (target false k).val := by dsimp [target];omega
   have ix : (target false k).val-1=(sourceIndex false k).val := by dsimp [target,sourceIndex];omega
   have iz : (target false k).val=(currentIndex k).val := by dsimp [target,currentIndex];omega
   rw [value,if_neg h9,if_pos h1,ix,iz,look_fin,look_fin]
   rfl
 · have h9 : (9 : Nat) ≤ (target true k).val := by dsimp [target];omega
   have ix : (target true k).val-1=(sourceIndex true k).val := by dsimp [target,sourceIndex];omega
   have iz : (target true k).val-8=(currentIndex k).val := by dsimp [target,currentIndex];omega
   rw [value,if_pos h9,ix,iz,look_fin,look_fin]
   rfl
def targetJob (job : Job) : Fin 17 := target job.1 job.2
theorem model_run (c : Context) (z succ : Fin 16 → NQ) (xs : List Job) (before : Fin 17 → K) :
 xs.foldl (fun before job=>NJL_PathStep.modelStep c z succ job.1 job.2 before) before=
 (xs.map targetJob).foldl (fun before i=>NJL_WriteFrame.write before i (value c z succ i)) before := by
 induction xs generalizing before with
 | nil => rfl
 | cons job js ih =>
   simpa only [List.foldl_cons,List.map_cons,NJL_PathStep.modelStep,targetJob,target_value] using
    ih (NJL_PathStep.modelStep c z succ job.1 job.2 before)
theorem full_mem (i : Fin 17) : i∈jobs.map targetJob ↔ i.val≠0 := by
 fin_cases i <;> decide
/-- Sixteen distinct writes, with the head cell fully framed. Constant small
index registry only; no concrete field recurrence is reduced. -/
theorem source (c : Context) (z succ : Fin 16 → NQ) (before : State)
 (hc : Domain c) (hz : ∀ i,Canon (z i)) (hs : ∀ i,Canon (succ i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJL_PathTrace.run c z succ jobs before=ok after ∧ NJL_PathTrace.Trace c z succ jobs before after ∧
 (∀ i,Canon (after i)) ∧ (∀ i,decode (after i)=if i.val≠0 then value c z succ i else decode (before i)) := by
 obtain ⟨after,call,trace,ha,va⟩ := NJL_PathTrace.source c z succ jobs before hc hz hs hb
 refine ⟨after,call,trace,ha,?_⟩
 intro i
 have point := congrFun va i
 rw [model_run,NJL_WriteFrame.fold] at point
 simpa only [full_mem] using point
#print axioms look_fin
#print axioms target_value
#print axioms model_run
#print axioms full_mem
#print axioms source
end AspisR1.NJL_PathFrame
end
