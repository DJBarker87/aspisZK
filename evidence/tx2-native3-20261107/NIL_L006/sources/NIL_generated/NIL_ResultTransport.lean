import NIL_Carriers
set_option autoImplicit false
noncomputable section
namespace NIL_ResultTransport
open Aeneas Aeneas.Std Result NIL_Carriers

theorem outer_bind {A B C : Type} (f : B → C) (m : Result A) (next : A → Result B) :
 outer f (do let x ← m;next x)=(do let x ← m;outer f (next x)) := by cases m <;> rfl

theorem outer_comp {A B C : Type} (f : A → B) (g : B → C) (m : Result A) :
 outer g (outer f m)=outer (fun x=>g (f x)) m := by cases m <;> rfl

theorem outer_roundtrip {A B : Type} (f : A → B) (g : B → A)
 (law : ∀ x,g (f x)=x) (m : Result A) : outer g (outer f m)=m := by
 cases m <;> simp only [outer,law]

theorem inner_roundtrip {A B : Type} (f : A → B) (g : B → A)
 (law : ∀ x,g (f x)=x) (m : core.result.Result A Fresh.Err) : unInner g (NIL_Carriers.inner f m)=m := by
 cases m <;> simp only [NIL_Carriers.inner,unInner,law,error_roundtrip]

theorem outer_injective {A B : Type} (f : A → B) (g : B → A)
 (law : ∀ x,g (f x)=x) {m n : Result A} (h : outer f m=outer f n) : m=n := by
 have h' := congrArg (outer g) h
 simpa only [outer_roundtrip f g law] using h'

theorem inner_injective {A B : Type} (f : A → B) (g : B → A)
 (law : ∀ x,g (f x)=x) {m n : core.result.Result A Fresh.Err} (h : NIL_Carriers.inner f m=NIL_Carriers.inner f n) : m=n := by
 have h' := congrArg (unInner g) h
 simpa only [inner_roundtrip f g law] using h'

theorem outer_ok_iff {A B : Type} (f : A → B) (m : Result A) (b : B) :
 outer f m=ok b ↔ ∃ a,m=ok a ∧ f a=b := by
 cases m <;> simp [outer]

theorem array_comp {A B C : Type} {N : Usize} (f : A → B) (g : B → C) (a : Array A N) :
 array g (array f a)=array (fun x=>g (f x)) a := by apply Subtype.ext;exact List.map_map

theorem array_roundtrip {A B : Type} {N : Usize} (f : A → B) (g : B → A)
 (law : ∀ x,g (f x)=x) (a : Array A N) : array g (array f a)=a := by
 apply Subtype.ext
 simp only [array,List.map_map,Function.comp_def,law,List.map_id]
 change List.map id a.val=a.val
 exact List.map_id _

theorem vec_roundtrip {A B : Type} (f : A → B) (g : B → A)
 (law : ∀ x,g (f x)=x) (a : alloc.vec.Vec A) : vec g (vec f a)=a := by
 apply Subtype.ext
 simp only [vec,List.map_map,Function.comp_def,law,List.map_id]
 change List.map id a.val=a.val
 exact List.map_id _
#print axioms outer_bind
#print axioms outer_comp
#print axioms outer_roundtrip
#print axioms inner_roundtrip
#print axioms outer_injective
#print axioms inner_injective
#print axioms outer_ok_iff
#print axioms array_comp
#print axioms array_roundtrip
#print axioms vec_roundtrip
end NIL_ResultTransport
