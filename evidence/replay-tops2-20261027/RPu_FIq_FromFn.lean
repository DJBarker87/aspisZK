import RPu_FIq_Native03
import OraclePortStdBuilder
open Aeneas Aeneas.Std Result
namespace FIq_Native
/-- Ordered from_fn interpretation. Copy/dummy are erased by Rust's constructor. -/
def array_from_fn_copy {T F : Type} (N : Usize) (_copy : core.marker.Copy T)
    (fn : core.ops.function.FnMut F Usize T) (_dummy : T) (f : F) : Result (Array T N) :=
  AspisR1.OraclePortStdBuilder.fromFn N fn f
#print axioms array_from_fn_copy
end FIq_Native
