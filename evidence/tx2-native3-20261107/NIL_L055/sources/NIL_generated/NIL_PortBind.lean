import NIL_TryTransport
import NIL_ResultCases
set_option autoImplicit false
noncomputable section
namespace NIL_PortBind
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse

theorem source {A B C D : Type} (u : A → B) (f : C → D) (m : Result A)
 (left : B → Result C) (right : A → Result D)
 (h : ∀ x,outer f (left (u x))=right x) :
 outer f (do let x ← outer u m;left x)=(do let x ← m;right x) := by
 rw [bind_outer,outer_bind]
 exact NIL_ResultCases.bind_congr m _ _ h

theorem read {A B C D R S : Type} (u : A → B) (ur : R → S) (f : C → D)
 (m : Result (core.result.Result A Cohort.Err × R))
 (left : B → S → Result (core.result.Result C Fresh.Err))
 (right : A → R → Result (core.result.Result D Cohort.Err))
 (h : ∀ x r,outer (NIL_Carriers.inner f) (left (u x) (ur r))=right x r) :
 outer (NIL_Carriers.inner f)
 (do let (value,r) ← outer (fun p=>(unInner u p.1,ur p.2)) m
     NIL_TryTransport.fresh value (fun x=>left x r))=
 (do let (value,r) ← m
     NIL_TryTransport.cohort value (fun x=>right x r)) := by
 apply source (fun p=>(unInner u p.1,ur p.2)) (NIL_Carriers.inner f) m
 intro p
 rcases p with ⟨value,r⟩
 change outer (NIL_Carriers.inner f) (NIL_TryTransport.fresh (unInner u value) (fun x=>left x (ur r)))=_
 rw [NIL_TryTransport.map_try]
 cases value with
 | Ok x => exact h x r
 | Err err => rfl
#print axioms source
#print axioms read
end NIL_PortBind
