import NJX_RangeFold
import NJL_WriteFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_RangeModel
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode K)
open NJX_RangeStep (index)
def value (xs : Fin 10 → NQ) (i : Fin 10) : K := decode (xs i)*decode (xs i)-decode (xs i)
def closed (view : Fin 3) (xs : Fin 10 → NQ) (old : Fin 33 → K) (j : Fin 33) : K :=
 if h : 10*view.val≤j.val ∧ j.val<10*view.val+10 then value xs ⟨j.val-10*view.val,by omega⟩ else old j

theorem membership (view : Fin 3) (j : Fin 33) :
 j∈(List.finRange 10).map (index view) ↔ 10*view.val≤j.val ∧ j.val<10*view.val+10 := by
 constructor
 · intro h
   obtain ⟨i,hi,eq⟩:=List.mem_map.mp h
   have v:=congrArg Fin.val eq
   dsimp [index] at v
   have h:=i.isLt
   omega
 · intro h
   let i : Fin 10:=⟨j.val-10*view.val,by omega⟩
   apply List.mem_map.mpr
   refine ⟨i,by simp,?_⟩
   apply Fin.ext
   dsimp [index,i]
   omega

theorem at_index (view : Fin 3) (xs : Fin 10 → NQ) (i : Fin 10) :
 closed view xs (fun _=>0) (index view i)=value xs i := by
 have hi:=i.isLt
 have bounds : 10*view.val≤(index view i).val ∧ (index view i).val<10*view.val+10 := by dsimp [index];omega
 rw [closed,if_pos bounds]
 congr 1
 apply Fin.ext
 dsimp [index]
 omega

/-- Symbolic frame/overwrite proof; no unfolding of a33×10concrete table. -/
theorem source (view : Fin 3) (xs : Fin 10 → NQ) (old : Fin 33 → K) :
 (List.finRange 10).foldl (fun s i=>NJX_RangeFold.modelStep view xs i s) old=closed view xs old := by
 let values:=closed view xs (fun _=>0)
 have step : (fun (s : Fin 33 → K) (i : Fin 10)=>NJX_RangeFold.modelStep view xs i s)=
  (fun s i=>NJL_WriteFrame.write s (index view i) (values (index view i))) := by
  funext s i j
  rw [show values (index view i)=value xs i from at_index view xs i]
  simp only [NJX_RangeFold.modelStep,NJL_WriteFrame.write,Function.update_apply,value,eq_comm]
 rw [step]
 have mapped : (List.finRange 10).foldl (fun s i=>NJL_WriteFrame.write s (index view i) (values (index view i))) old=
  ((List.finRange 10).map (index view)).foldl (fun s i=>NJL_WriteFrame.write s i (values i)) old := by rw [List.foldl_map]
 rw [mapped]
 funext j
 rw [NJL_WriteFrame.fold]
 by_cases h : 10*view.val≤j.val ∧ j.val<10*view.val+10
 · rw [if_pos ((membership view j).mpr h)]
   simp only [values,closed,if_pos h]
 · rw [if_neg (fun hm=>h ((membership view j).mp hm))]
   simp only [closed,if_neg h]
#print axioms membership
#print axioms at_index
#print axioms source
end AspisR1.NKI_RangeModel
end
