import NCX_Reference.Funs
set_option autoImplicit false
namespace NCX_Status
open Aeneas Aeneas.Std Result

theorem active : NCX_Reference.status 1#u8=ok (.Ok .Active) := by
  have h0 : (1#u8 : U8) ≠ (⟨0#8⟩ : U8) := by decide
  have h1 : (1#u8 : U8) = (⟨1#8⟩ : U8) := by decide
  have h2 : (1#u8 : U8) ≠ (⟨2#8⟩ : U8) := by decide
  have h3 : (1#u8 : U8) ≠ (⟨3#8⟩ : U8) := by decide
  unfold NCX_Reference.status
  split <;> simp_all
#print axioms active
end NCX_Status
