import NNG_Front087
import NNG_Erase087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Factor087
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps NMT_CallTree

theorem bind_assoc {A B C : Type} (code : Code A) (f : A → Code B) (g : B → Code C) :
 NMT_CallTree.bind (NMT_CallTree.bind code f) g=NMT_CallTree.bind code (fun a=>NMT_CallTree.bind (f a) g) := by
 induction code with
 | done a=>rfl
 | plain r next ih=>
   change Code.plain r (fun a=>NMT_CallTree.bind (NMT_CallTree.bind (next a) f) g)=Code.plain r (fun a=>NMT_CallTree.bind (next a) (fun b=>NMT_CallTree.bind (f b) g))
   exact congrArg (Code.plain r) (funext ih)
 | call site args r next ih=>
   change Code.call site args r (fun a=>NMT_CallTree.bind (NMT_CallTree.bind (next a) f) g)=Code.call site args r (fun a=>NMT_CallTree.bind (next a) (fun b=>NMT_CallTree.bind (f b) g))
   exact congrArg (Code.call site args r) (funext ih)

def finish {H W : Type} (c : Calls) (s : Parent H W) (r : NNG_Front087.FrontOut H) : Code PreparedOut :=
 match r with | .Err e=>pure (.Err e,s.scratch) | .Ok (sem,v)=>NNG_Tree087.mark c s v sem

theorem observed {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) :
 NMT_CallTree.bind (NNG_Front087.observed c s v) (finish c s)=NNG_Tree087.observed c s v := by
 unfold NNG_Front087.observed NNG_Tree087.observed
 simp only [Bind.bind]
 rw [bind_assoc]
 apply congrArg (NMT_CallTree.bind _)
 funext r
 cases r <;> rfl

theorem view {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) :
 NMT_CallTree.bind (NNG_Front087.view c s semantic y1) (finish c s)=NNG_Tree087.view c s semantic y1 := by
 unfold NNG_Front087.view NNG_Tree087.view
 simp only [Bind.bind]
 rw [bind_assoc]
 apply congrArg (NMT_CallTree.bind _)
 funext r
 cases r with
 | Err e=>rfl
 | Ok v=>exact observed c s v

theorem values {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) :
 NMT_CallTree.bind (NNG_Front087.values c s semantic y1 back vecBack) (finish c s)=NNG_Tree087.values c s semantic y1 back vecBack := by
 unfold NNG_Front087.values NNG_Tree087.values
 simp only [Bind.bind]
 rw [bind_assoc]
 apply congrArg (NMT_CallTree.bind _)
 funext src
 rw [bind_assoc]
 apply congrArg (NMT_CallTree.bind _)
 funext pair
 rcases pair with ⟨r,after⟩
 cases r with
 | Err e=>rfl
 | Ok u=>
   rw [bind_assoc]
   apply congrArg (NMT_CallTree.bind _)
   funext semantic
   rw [bind_assoc]
   apply congrArg (NMT_CallTree.bind _)
   funext y1
   exact view c s semantic y1

theorem semantic {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) :
 NMT_CallTree.bind (NNG_Front087.semantic c s semantic y1 back vecBack) (finish c s)=NNG_Tree087.semantic c s semantic y1 back vecBack := by
 unfold NNG_Front087.semantic NNG_Tree087.semantic
 simp only [Bind.bind]
 rw [bind_assoc]
 apply congrArg (NMT_CallTree.bind _)
 funext src
 rw [bind_assoc]
 apply congrArg (NMT_CallTree.bind _)
 funext pair
 rcases pair with ⟨r,after⟩
 cases r with
 | Err e=>rfl
 | Ok u=>exact values c s after y1 back vecBack

theorem split {H W : Type} (c : Calls) (s : Parent H W) (logical : alloc.vec.Vec U8) :
 NMT_CallTree.bind (NNG_Front087.split c s logical) (finish c s)=NNG_Tree087.split c s logical := by
 unfold NNG_Front087.split NNG_Tree087.split
 simp only [Bind.bind]
 rw [bind_assoc]
 apply congrArg (NMT_CallTree.bind _)
 funext pair
 rcases pair with ⟨⟨left,right⟩,back⟩
 exact semantic c s left right back (alloc.vec.Vec.deref_mut logical).2

theorem tree {H W : Type} (c : Calls) (s : Parent H W) :
 NMT_CallTree.bind (NNG_Front087.tree c s) (finish c s)=NNG_Tree087.tree c s := by
 unfold NNG_Front087.tree NNG_Tree087.tree
 simp only [Bind.bind]
 rw [bind_assoc]
 apply congrArg (NMT_CallTree.bind _)
 funext r
 cases r with
 | Err e=>rfl
 | Ok logical=>exact split c s logical
#print axioms bind_assoc
#print axioms observed
#print axioms view
#print axioms values
#print axioms semantic
#print axioms split
#print axioms tree
end AspisR1.NNG_Factor087
