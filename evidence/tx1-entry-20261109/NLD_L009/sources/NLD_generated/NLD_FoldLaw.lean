import NLD_CutFold
set_option autoImplicit false
namespace AspisR1.NLD
open Aeneas Aeneas.Std Result
/-- NHZ-shaped fold with the larger entry event carrier. No root is discharged
by assuming this tree: concrete occurrences must construct it. -/
theorem events_from_cuts {A : Type} {p : Program A} {s t : ParentState}
    {r : Result A} {events : List Event} (cuts : Cuts p s r t events) :
    run p s = (r,t,events) := by
  induction cuts with
  | done => rfl
  | next site action k pre post final b result tail head rest ih =>
    simp only [run, head, ih]
  | fail site action k pre post e head => simp only [run,head]
  | div site action k pre post head => simp only [run,head]

/-- Every interpreted program has a source-order cut derivation. This proves
model completeness only; it cannot produce native harness certificates. -/
theorem cuts_from_run {A : Type} (p : Program A) (s : ParentState) :
    Cuts p s (run p s).1 (run p s).2.1 (run p s).2.2 := by
  induction p generalizing s with
  | done a => exact .done a s
  | @step B site action k ih =>
    cases h : action s with
    | mk out post =>
      cases out with
      | ok b =>
        simp only [run,h]
        exact .next site action k s post _ b _ _ h (ih b post post)
      | fail e =>
        simp only [run,h]
        exact .fail site action k s post e h
      | div =>
        simp only [run,h]
        exact .div site action k s post h

/-- Determinism is for the same program and SAME initial state only. -/
theorem same_run {A : Type} {p : Program A} {s t u : ParentState}
    {r q : Result A} {xs ys : List Event}
    (left : Cuts p s r t xs) (right : Cuts p s q u ys) :
    (r,t,xs) = (q,u,ys) := (events_from_cuts left).symm.trans (events_from_cuts right)

#print axioms events_from_cuts
#print axioms cuts_from_run
#print axioms same_run
end AspisR1.NLD
