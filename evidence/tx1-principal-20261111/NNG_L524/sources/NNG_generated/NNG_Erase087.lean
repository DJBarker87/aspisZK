import NNG_Tree087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Erase087
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps NMT_CallTree

theorem prepared {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H) :
 erase (NNG_Tree087.prepared c s v sem)=NMP_PrepareSuffix.f7 c s v sem := by
 simp only [NNG_Tree087.prepared,NMP_PrepareSuffix.f7,erase_invoke]
theorem mark {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H) :
 erase (NNG_Tree087.mark c s v sem)=NMP_PrepareSuffix.f6 c s v sem := by
 simp only [NNG_Tree087.mark,NMP_PrepareSuffix.f6,Bind.bind,erase_bind,erase_invoke,prepared]
theorem observed {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) :
 erase (NNG_Tree087.observed c s v)=NMP_PrepareSuffix.f5 c s v := by
 unfold NNG_Tree087.observed NMP_PrepareSuffix.f5
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro r
 cases r <;> simp only [erase_pure,mark]
theorem view {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) :
 erase (NNG_Tree087.view c s semantic y1)=NMP_PrepareSuffix.f4 c s semantic y1 := by
 unfold NNG_Tree087.view NMP_PrepareSuffix.f4
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro r
 cases r <;> simp only [erase_pure,observed]

theorem values {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) :
 erase (NNG_Tree087.values c s semantic y1 back vecBack)=NMP_PrepareSuffix.f3 c s semantic y1 back vecBack := by
 unfold NNG_Tree087.values NMP_PrepareSuffix.f3
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
 erase (NNG_Tree087.semantic c s semantic y1 back vecBack)=NMP_PrepareSuffix.f2 c s semantic y1 back vecBack := by
 unfold NNG_Tree087.semantic NMP_PrepareSuffix.f2
 simp only [Bind.bind]
 rw [erase_bind,erase_lift]
 apply result_congr
 intro src
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro pair
 rcases pair with ⟨r,after⟩
 cases r <;> simp only [erase_pure,values]

theorem split {H W : Type} (c : Calls) (s : Parent H W) (logical : alloc.vec.Vec U8) :
 erase (NNG_Tree087.split c s logical)=NMP_PrepareSuffix.f1 c s logical := by
 unfold NNG_Tree087.split NMP_PrepareSuffix.f1
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro pair
 rcases pair with ⟨⟨left,right⟩,back⟩
 exact semantic c s left right back (alloc.vec.Vec.deref_mut logical).2

theorem tree {H W : Type} (c : Calls) (s : Parent H W) :
 erase (NNG_Tree087.tree c s)=NMP_PrepareSuffix.f0 c s := by
 unfold NNG_Tree087.tree NMP_PrepareSuffix.f0
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro r
 cases r <;> simp only [erase_pure,split]
#print axioms prepared
#print axioms mark
#print axioms observed
#print axioms view
#print axioms values
#print axioms semantic
#print axioms split
#print axioms tree
end AspisR1.NNG_Erase087
