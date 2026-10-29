import NEF_BackendRef.Funs
set_option autoImplicit false
namespace NEF_EmittedBackend
open Aeneas Aeneas.Std Result NEF_BackendRef
/-- The two independently extracted Rust bodies are definitionally identical
once the one backend argument is statically selected. Includes all errors. -/
theorem specialisation {O : Type} (ops : Ops O) (x : CM) :
    inv_with_ref ops x ops.inv = inv_static_ref ops x := rfl

theorem selected_backend {O : Type} (ops : Ops O) (x : CM)
    (backend : U32 → Result U32) (selected : backend = ops.inv) :
    inv_with_ref ops x backend = inv_static_ref ops x := by
  rw [selected]
  rfl

theorem contextual {O R : Type} (ops : Ops O) (x : CM)
    (continuation : CM → Result R) :
    (do let y ← inv_with_ref ops x ops.inv; continuation y) =
    (do let y ← inv_static_ref ops x; continuation y) := rfl
#print axioms specialisation
#print axioms selected_backend
#print axioms contextual
end NEF_EmittedBackend
