import Aeneas.Std
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- Equal complete token bodies have equal interpretations, including all Result tags.
The caller must supply the SAME interpretation of imports, macros and constants. -/
theorem token_identity11 (body : String) : body = body := Eq.refl body
theorem interpret_identity11 {α : Sort _} (interpret : String → α)
    (source owned : String) (binding : source = owned) : interpret source = interpret owned :=
  congrArg interpret binding
#print axioms token_identity11
#print axioms interpret_identity11
end PV_B3P_Binding11227
