import NIL_ResultReverse
set_option autoImplicit false
namespace NIL_ResultCases
open Aeneas Aeneas.Std Result NIL_Carriers

theorem outer_ok {A B : Type} (f : A → B) (x : A) : outer f (ok x)=ok (f x) := rfl
theorem outer_fail {A B : Type} (f : A → B) (err : Error) : outer f (fail err)=fail err := rfl
theorem outer_div {A B : Type} (f : A → B) : outer f div=div := rfl
theorem inner_ok {A B : Type} (f : A → B) (x : A) : NIL_Carriers.inner f (.Ok x)=.Ok (f x) := rfl
theorem inner_err {A B : Type} (f : A → B) (err : Fresh.Err) : NIL_Carriers.inner f (.Err err)=.Err (error err) := rfl
#print axioms outer_ok
#print axioms outer_fail
#print axioms outer_div
#print axioms inner_ok
#print axioms inner_err
end NIL_ResultCases
