import PV_B3P_ClosureLinks14227
namespace PV_B3Q_Wrapping
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
inductive Body where | add | sub | mul
def Signature (ty : UScalarTy) : Body → Type := fun _ => UScalar ty → UScalar ty → Result (UScalar ty)
/-- Each deployed uint_macros body forwards both operands unchanged to exactly
one intrinsic. Intrinsic and machine semantics remain V370 / D381,D386. -/
def source (ty : UScalarTy) : (i : Body) → Signature ty i
 | .add => fun x y => .ok (UScalar.wrapping_add x y)
 | .sub => fun x y => .ok (UScalar.wrapping_sub x y)
 | .mul => fun x y => .ok (UScalar.wrapping_mul x y)
def model (ty : UScalarTy) : (i : Body) → Signature ty i
 | .add => fun x y => lift (UScalar.wrapping_add x y)
 | .sub => fun x y => lift (UScalar.wrapping_sub x y)
 | .mul => fun x y => lift (UScalar.wrapping_mul x y)
theorem wrappers_link (ty : UScalarTy) : PV_B3P_Link_std_dependency_closure14
    (Signature ty) (source ty) (model ty) := by
 intro body
 cases body <;> rfl
#print axioms wrappers_link
end PV_B3Q_Wrapping
