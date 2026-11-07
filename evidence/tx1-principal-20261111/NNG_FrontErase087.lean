import NNG_FrontValue087
import NNG_Front087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FrontErase087
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps NMT_CallTree

theorem observed {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) :
 erase (NNG_Front087.observed c s v)=NNG_FrontValue087.observed c s v := by
 unfold NNG_Front087.observed NNG_FrontValue087.observed
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro r
 cases r <;> rfl

theorem view {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) :
 erase (NNG_Front087.view c s semantic y1)=NNG_FrontValue087.view c s semantic y1 := by
 unfold NNG_Front087.view NNG_FrontValue087.view
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro r
 cases r <;> simp only [erase_pure,observed]

theorem values {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) :
 erase (NNG_Front087.values c s semantic y1 back vecBack)=NNG_FrontValue087.values c s semantic y1 back vecBack := by
 unfold NNG_Front087.values NNG_FrontValue087.values
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro src
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro pair
 rcases pair with ⟨r,after⟩
 cases r with
 | Err e=>rfl
 | Ok u=>
   rw [erase_bind,erase_lift]
   apply result_congr
   intro fullSemantic
   rw [erase_bind,erase_lift]
   apply result_congr
   intro fullY1
   exact view c s fullSemantic fullY1

theorem semantic {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) :
 erase (NNG_Front087.semantic c s semantic y1 back vecBack)=NNG_FrontValue087.semantic c s semantic y1 back vecBack := by
 unfold NNG_Front087.semantic NNG_FrontValue087.semantic
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro src
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro pair
 rcases pair with ⟨r,after⟩
 cases r <;> simp only [erase_pure,values] <;> rfl

theorem split {H W : Type} (c : Calls) (s : Parent H W) (logical : alloc.vec.Vec U8) :
 erase (NNG_Front087.split c s logical)=NNG_FrontValue087.split c s logical := by
 unfold NNG_Front087.split NNG_FrontValue087.split
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro pair
 rcases pair with ⟨⟨left,right⟩,back⟩
 exact semantic c s left right back (alloc.vec.Vec.deref_mut logical).2

theorem tree {H W : Type} (c : Calls) (s : Parent H W) :
 erase (NNG_Front087.tree c s)=NNG_FrontValue087.tree c s := by
 unfold NNG_Front087.tree NNG_FrontValue087.tree
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro r
 cases r <;> simp only [erase_pure,split]
#print axioms observed
#print axioms view
#print axioms values
#print axioms semantic
#print axioms split
#print axioms tree
end AspisR1.NNG_FrontErase087
