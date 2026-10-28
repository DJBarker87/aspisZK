import NCX_Reference.Funs
set_option autoImplicit false
namespace NCX_StatusSpec
open Aeneas Aeneas.Std Result

theorem value (v : U8) : NCX_Reference.status v=ok
    (if v=0#u8 then .Ok .Pending else if v=1#u8 then .Ok .Active else
     if v=2#u8 then .Ok .Paused else if v=3#u8 then .Ok .Retired else .Err .InvalidStatus) := by
  have h0 : (⟨0#8⟩ : U8)=0#u8 := by decide
  have h1 : (⟨1#8⟩ : U8)=1#u8 := by decide
  have h2 : (⟨2#8⟩ : U8)=2#u8 := by decide
  have h3 : (⟨3#8⟩ : U8)=3#u8 := by decide
  unfold NCX_Reference.status
  split <;> simp_all
#print axioms value
end NCX_StatusSpec
