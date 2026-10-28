import R1Z.PV_CBL_StringViewValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RL_V179
set_option autoImplicit false
/-- Read-only view at the existing String carrier boundary. -/
def nativeView (s : String) : Result String := ok s
theorem complete (s : String) :
    nativeView s=PV_CBL_StringOwnedReference.string_owned_reference s := rfl
theorem observer {A : Type} (f : String → A) (s : String) :
    (do let p ← nativeView s; ok (f p)) =
    (do let p ← PV_CBL_StringOwnedReference.string_owned_reference s; ok (f p)) := rfl
theorem nonvacuous : nativeView ""=ok "" ∧ nativeView "a/é"=ok "a/é" := ⟨rfl,rfl⟩
#print axioms complete
#print axioms observer
#print axioms nonvacuous
end R1Z.PV_RL_V179
