import NJS_Extract.Funs
import NDI_BatchRun
set_option autoImplicit false
namespace NJS_Swap
open Aeneas Aeneas.Std Result
abbrev Keys := Array U64 16#usize

def run (keys : Keys) (i j : Usize) : Result Keys := do
 let (s,back)←lift (Array.to_slice_mut keys)
 let out←core.slice.Slice.swap s i j
 ok (back out)

theorem value (keys : Keys) (i j : Usize) (hi : i.val<16) (hj : j.val<16) :
 ∃ out,run keys i j=ok out ∧ out=(keys.set i keys.val[j.val]!).set j keys.val[i.val]! := by
 have hlen : keys.val.length=16 := keys.property
 obtain ⟨slice,swapped,length,left,right,frame⟩ := WP.spec_imp_exists
   (core.slice.Slice.swap_spec keys.to_slice i j
     (by simpa [Slice.length,hlen] using hi) (by simpa [Slice.length,hlen] using hj))
 let out := keys.from_slice slice
 have values : out.val=slice.val := by
   dsimp [out]
   simp only [Array.from_slice]
   have same : slice.val.length=(16#usize).val := by simpa [Slice.length] using length
   simp only [same,dif_pos]
 refine ⟨out,?_,?_⟩
 · simp [run,Array.to_slice_mut,lift,swapped,out]
 · apply Subtype.ext
   apply List.ext_getElem
   · exact out.property.trans ((keys.set i keys.val[j.val]!).set j keys.val[i.val]!).property.symm
   · intro k hk he
     have kb : k<16 := by have := out.property;omega
     have cells : out.val[k]! = ((keys.set i keys.val[j.val]!).set j keys.val[i.val]!).val[k]! := by
       rw [NDI_BatchStep.frame (keys.set i keys.val[j.val]!) j keys.val[i.val]! k kb,
         NDI_BatchStep.frame keys i keys.val[j.val]! k kb]
       by_cases kj : k=j.val
       · subst k
         simpa only [if_pos rfl,values,Array.to_slice] using right
       · by_cases ki : k=i.val
         · subst k
           simpa only [if_neg kj,if_pos rfl,values,Array.to_slice] using left
         · simpa only [if_neg kj,if_neg ki,values,Array.to_slice] using frame k ki kj
     simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hk,
       List.getElem?_eq_getElem he,Option.getD_some] using cells
#print axioms value
end NJS_Swap
