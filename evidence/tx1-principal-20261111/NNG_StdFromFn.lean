import NNG_StdArray
set_option autoImplicit false
namespace AspisR1.NNG_StdArray
open Aeneas Aeneas.Std Result NNG_verify_finish
/-- The accepted generic std adapter has precisely the fresh opaque signature. -/
def implementation : ∀ {T F : Type} (n : Usize), core.ops.function.FnMut F Usize T → F → Result (Array T n) :=
 @OraclePortStdBuilder.fromFn
end AspisR1.NNG_StdArray
