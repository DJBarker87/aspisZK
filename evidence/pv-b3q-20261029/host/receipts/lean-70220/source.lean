import PV_B3P_ClosureLinks14227
namespace PV_B3Q_StdValues
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
inductive Body where | from_output | identity_from | usize_clone | bool_clone
/-- A borrowed primitive value is represented by its immutable contents. Native
pointer realization remains V370. Both primitive Clone impls simply read it. -/
def Signature (T E : Type) : Body → Type
 | .from_output => T → Result (core.result.Result T E)
 | .identity_from => T → Result T
 | .usize_clone => Usize → Result Usize
 | .bool_clone => Bool → Result Bool
def source (T E : Type) : (i : Body) → Signature T E i
 | .from_output => fun output => .ok (.Ok output)
 | .identity_from => fun value => .ok value
 | .usize_clone => fun borrowed => .ok borrowed
 | .bool_clone => fun borrowed => .ok borrowed
def model (T E : Type) : (i : Body) → Signature T E i
 | .from_output => fun output => .ok (.Ok output)
 | .identity_from => Result.ok
 | .usize_clone => Result.ok
 | .bool_clone => Result.ok
theorem values_link (T E : Type) : PV_B3P_Link_std_dependency_closure14
    (Signature T E) (source T E) (model T E) := by
 intro i
 cases i <;> rfl
#print axioms values_link
end PV_B3Q_StdValues
