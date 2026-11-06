import Aeneas
set_option autoImplicit false
namespace NJI_LengthCuts
open Aeneas Aeneas.Std Result

/-- Constructor/scalar first stage. Native credit is restricted to the five
explicit frozen record/error monomorphizations, not arbitrary Rust carriers. -/
def gate {T E : Type} (len width : Usize) (error : E) :
 Option (core.result.Result T E) :=
 if len=width then none else some (.Err error)

theorem entered {T E : Type} (width : Usize) (error : E) :
 gate (T:=T) width width error=none := by simp [gate]

theorem rejected {T E : Type} (len width : Usize) (error : E) (wrong : len≠width) :
 gate (T:=T) len width error=some (.Err error) := by simp [gate,wrong]

/-- The existing P7 Slice.len law supplies the same descriptor, with no payload
read. This handles256/320 and every other wrong caller length without a fake
allocation or a bound on the buffer. -/
theorem slice_rejected {T E : Type} (b : Slice U8) (width : Usize) (error : E)
 (wrong : b.val.length≠width.val) :
 gate (T:=T) (Slice.len b) width error=some (.Err error) := by
 apply rejected
 intro same
 exact wrong (congrArg UScalar.val same)

#print axioms entered
#print axioms rejected
#print axioms slice_rejected
end NJI_LengthCuts
