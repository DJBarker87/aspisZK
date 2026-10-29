import R1Z.PV_RDB2F_ByteArray
import R1Z.PV_RDB2F_GenericArrayStorage
import R1Z.PV_RDB2F_VerifierCalls
import R1Z.PV_RDB2F_ShaNiOuter
namespace R1Z.PV_RDB2F_NativeLoanFrame
open Aeneas Aeneas.Std Result PV_RDB2F_ByteArray
set_option autoImplicit false
/-- Actual address-level frame for distinct mutable byte loans, used by padding
and output serialization. This concerns current memory, rather than record names. -/
theorem disjoint_stores_commute (mem : Memory) (p q : Nat) (x y : U8) (ne : p≠q) :
    store (store mem p x) q y=store (store mem q y) p x := by
  funext a
  by_cases hp : a=p <;> by_cases hq : a=q <;> simp_all [store]

theorem current_output_preserves_buffer (mem : Memory) (out buffer : Nat) (value : U8)
    (separate : buffer≠out) : store mem out value buffer=mem buffer :=
  other_allocation mem out buffer value separate

#print axioms disjoint_stores_commute
#print axioms current_output_preserves_buffer
end R1Z.PV_RDB2F_NativeLoanFrame
