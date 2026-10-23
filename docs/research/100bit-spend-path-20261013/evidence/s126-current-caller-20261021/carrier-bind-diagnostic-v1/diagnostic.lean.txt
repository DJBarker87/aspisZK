import CurrentOriginalPreparedNativeV1
open Aeneas Aeneas.Std Result
#print bind_tc_ok
#print bind_assoc_eq
#print Aeneas.Result.bind
#print instBindResult
example {A B C : Type} (a : A) (b : B) (f : A → B → Result C) :
    (do let (x,y) ← (let (u,v):=(a,b); ok (u,v)); f x y)=f a b := by
  rfl
