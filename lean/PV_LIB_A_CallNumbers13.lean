import PV_LIB_A_CallFrame13
set_option autoImplicit false
namespace PV_LIB_A_CallNumbers13
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Argument administration leaves the counter unchanged. This is a single
source push fact, not equality with a summarized callee's return counter. -/
theorem arguments_counter (s : Store Data) (child first : Nat) (args : List Data) :
    (PV_STX2_Native.arguments child args first s).nextActivation = s.nextActivation := by
  induction args generalizing s first with
  | nil => rfl
  | cons v vs ih => exact ih _ _

theorem issued_counter (s : Store Data) (args : List Data) :
    (PV_THR2_StaticCall.issued s args).nextActivation = s.nextActivation+1 :=
  arguments_counter _ _ _ _

/-- Every already-bounded caller remains below the next counter after this
actual fresh push; the fresh child is also below it. Existing live-numbering
stack-chain invariants still supply the saved callers' order. -/
theorem push_bounds (s : Store Data) (args : List Data) (a : Nat)
    (caller : a < s.nextActivation) :
    a < (PV_THR2_StaticCall.issued s args).nextActivation ∧
    s.nextActivation < (PV_THR2_StaticCall.issued s args).nextActivation := by
  rw [issued_counter]
  exact ⟨Nat.lt_trans caller (Nat.lt_succ_self _),Nat.lt_succ_self _⟩

#print axioms arguments_counter
#print axioms issued_counter
#print axioms push_bounds
end PV_LIB_A_CallNumbers13
