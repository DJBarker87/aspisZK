import NJS_Extract.Funs
import MultiproofSortRef.Funs
import NJS_Swap
import NJS_Leaves
import NBI_Sort
import Port3_Wrapping
set_option autoImplicit false
namespace NJS_SortStep
open Aeneas Aeneas.Std Result
theorem predecessor (j : Usize) (positive : 0<j.val) (small : j.val<16) :
 (Usize.wrapping_sub j 1#usize).val=j.val-1 := by
 rw [Usize.wrapping_sub_val_eq]
 have cap : 16<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have bound : j.val<UScalar.size .Usize := by omega
 change (j.val+(UScalar.size .Usize-1))%UScalar.size .Usize=j.val-1
 have eqv : j.val+(UScalar.size .Usize-1)=(j.val-1)+UScalar.size .Usize := by omega
 rw [eqv,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
abbrev Keys := Array U64 16#usize
open MultiproofSortRef AspisR1

def control : sort_reference.InsertStep → ControlFlow (Keys×Usize) Keys
 | .Done keys => .done keys | .Next keys j => .cont (keys,j)

theorem step (keys : Keys) (j : Usize) (bound : j.val<16) :
 ∃ observed,sort_reference.insert_step keys j=ok observed ∧
   NJS_Extract.verifier.candidate.sort_batch_keys_loop0_loop0.body keys j=ok (control observed) ∧
   NBI_Sort.NativeStep keys j observed := by
 by_cases zero : j=0#usize
 · subst j
   have post : NBI_Sort.NativeStep keys 0#usize (.Done keys) := ⟨rfl,Or.inl rfl⟩
   refine ⟨.Done keys,NBI_Sort.step_port keys 0#usize bound _ post,?_,post⟩
   simp [NJS_Extract.verifier.candidate.sort_batch_keys_loop0_loop0.body,control]
 · have positive : 0<j.val := by
     have ne : j.val≠0 := by intro h;exact zero (UScalar.eq_of_val_eq h)
     omega
   have guard : j>0#usize := positive
   obtain ⟨lower,sub,subPost⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=j) (y:=1#usize) (by scalar_tac))
   have lowerVal : lower.val=j.val-1 := by simpa only [show (1#usize).val=1 from rfl] using subPost.1
   have lowerEq : Usize.wrapping_sub j 1#usize=lower := by
     apply UScalar.eq_of_val_eq
     rw [predecessor j positive bound,lowerVal]
   have lowerBound : lower.val<16 := by omega
   obtain ⟨left,readLeft,leftValue⟩ := WP.spec_imp_exists (Array.index_usize_spec keys lower (by scalar_tac))
   obtain ⟨right,readRight,rightValue⟩ := WP.spec_imp_exists (Array.index_usize_spec keys j (by scalar_tac))
   have len : keys.val.length=16 := keys.property
   have leftVal : left=keys.val[lower.val]! := by
     simpa only [getElem!_pos keys.val lower.val (by omega)] using leftValue
   have rightVal : right=keys.val[j.val]! := by
     simpa only [getElem!_pos keys.val j.val (by omega)] using rightValue
   have body : NJS_Extract.verifier.candidate.sort_batch_keys_loop0_loop0.body keys j =
     if left>right then (do let out←NJS_Swap.run keys lower j;ok (ControlFlow.cont (out,lower)))
     else ok (ControlFlow.done keys) := by
     simp [NJS_Extract.verifier.candidate.sort_batch_keys_loop0_loop0.body,guard,
       NJS_Leaves.key,lowerEq,readLeft,readRight,NJS_Swap.run,Array.to_slice_mut,lift,bind_assoc_eq]
   by_cases compare : left>right
   · obtain ⟨out,swapRun,outEq⟩ := NJS_Swap.value keys lower j lowerBound bound
     have post : NBI_Sort.NativeStep keys j (.Next out lower) := by
       refine ⟨by omega,?_,outEq⟩
       simpa only [←leftVal,←rightVal] using compare
     refine ⟨.Next out lower,NBI_Sort.step_port keys j bound _ post,?_,post⟩
     simp only [body,if_pos compare,swapRun,bind_tc_ok,control]
   · have post : NBI_Sort.NativeStep keys j (.Done keys) := by
       refine ⟨rfl,Or.inr ?_⟩
       rw [←lowerVal,←leftVal,←rightVal]
       exact le_of_not_gt compare
     refine ⟨.Done keys,NBI_Sort.step_port keys j bound _ post,?_,post⟩
     simp only [body,if_neg compare,control]
#print axioms predecessor
#print axioms step
end NJS_SortStep
