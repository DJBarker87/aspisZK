import NJL_WindowPowerFrame
import NJL_CacheReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_WindowPowerOverwrite
open FIv_NativeArithmetic (NQ)
open NJL_WindowPowerFrame (State put)
/-- Pure8cell frame identity; no field operation or recurrence is unfolded. -/
theorem overwrite (before values : State) :
 ((List.finRange 8).zip (List.ofFn values)).foldl (fun state entry=>put state entry.1 entry.2) before=values := by
 have indices : List.finRange 8=[0,1,2,3,4,5,6,7] := rfl
 have cells : List.ofFn values=[values 0,values 1,values 2,values 3,values 4,values 5,values 6,values 7] := rfl
 rw [indices,cells]
 simp only [List.zip,List.foldl]
 funext i
 fin_cases i <;> simp [put,Fin.ext_iff]
theorem power_list {lambda : NQ} (p : NJL_CachedPowers.Packet lambda) :
 List.ofFn (NJL_CacheReads.power p)=p.powers := by
 apply List.ext_getElem
 · simp only [List.length_ofFn,p.eight]
 · intro i hi hj
   simp only [List.getElem_ofFn,NJL_CacheReads.power]
#print axioms overwrite
#print axioms power_list
end AspisR1.NJL_WindowPowerOverwrite
end
