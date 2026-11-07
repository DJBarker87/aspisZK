import NMT_CallTree
set_option autoImplicit false
namespace AspisR1.NMP_DirectBind
open Aeneas Aeneas.Std Result
theorem ok {A B : Type} (a : A) (k : A → Result B) :
 Aeneas.Std.bind (.ok a) k = k a := rfl
theorem fail {A B : Type} (e : Error) (k : A → Result B) :
 Aeneas.Std.bind (.fail e) k = .fail e := rfl
theorem div {A B : Type} (k : A → Result B) :
 Aeneas.Std.bind (.div : Result A) k = .div := rfl
#print axioms ok
#print axioms fail
#print axioms div
end AspisR1.NMP_DirectBind
