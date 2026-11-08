import LIBC_ResultGraph
set_option autoImplicit false
namespace AspisR1.NNH_Run5bReturnedGraph
open Aeneas Aeneas.Std Result

theorem ok {A B E : Type} (port : A → Except E B) (error : E)
 (model : Result A) (b : B)
 (returned : LIBC_ResultGraph.value port (.error error) model = .ok b) :
 ∃ a, model = .ok a ∧ port a = .ok b := by
 cases model with
 | fail e => cases returned
 | div => cases returned
 | ok a => exact ⟨a,rfl,returned⟩

theorem not_ok {A B E : Type} (port : A → Except E B) (error : E)
 (model : Result A) (a : A) (b : B) (e : E)
 (returned : LIBC_ResultGraph.value port (.error error) model = .error e)
 (value : port a = .ok b) : model ≠ .ok a := by
 intro h
 rw [h,LIBC_ResultGraph.value,value] at returned
 cases returned
#print axioms ok
#print axioms not_ok
end AspisR1.NNH_Run5bReturnedGraph
