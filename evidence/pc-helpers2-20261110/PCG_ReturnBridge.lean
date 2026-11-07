import PCG_ReturnRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_ReturnBridge
abbrev Reply := Option ((Array U8 32#usize) × (alloc.vec.Vec U8))
/-- Named runtime-return-data slot; values retain RuntimeReturnData trust. -/
abbrev RuntimeReturnData := Unit → Result Reply

theorem reference (reply : Reply) : PCG_ReturnRef.forward reply = ok reply := rfl

def native (runtime : RuntimeReturnData) : Result Reply := do
 let reply ← runtime ()
 PCG_ReturnRef.forward reply

/-- Includes None, full program key, every byte in order, length, and aborts.
The native ownership window establishes the same returned Vec allocation. -/
theorem row_345 (runtime : RuntimeReturnData) : native runtime = runtime () := by
 simp only [native,reference]
 cases runtime () <;> rfl

theorem some_exact (key : Array U8 32#usize) (bytes : alloc.vec.Vec U8) :
 PCG_ReturnRef.forward (some (key,bytes)) = ok (some (key,bytes)) := rfl

#print axioms reference
#print axioms row_345
#print axioms some_exact
end PCG_ReturnBridge
