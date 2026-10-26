import R1Z.ProverRw18ContextBounded
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextFuel
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes] [ExternalFuns]

theorem sufficient (lambda : Q) (values : Slice U32) (i : Nat) (out power : Q) :
    run lambda (⟨values,i⟩ : Iter) out power =
      ProverRw18InlineContext.bounded lambda (values.val.length-i+1) (⟨values,i⟩ : Iter) out power := by
  rw [ProverRw18ContextInduction.run,ProverRw18ContextBounded.bounded]
  rw [PV_RW_NativeForBound.exact_fuel]

theorem arity16 (lambda : Q) (values : Array U32 16#usize) (out power : Q) :
    run lambda (⟨Array.to_slice values,0⟩ : Iter) out power =
      ProverRw18InlineContext.bounded lambda 17 (⟨Array.to_slice values,0⟩ : Iter) out power := by
  rw [ProverRw18ContextInduction.run,ProverRw18ContextBounded.bounded]
  rw [PV_RW_NativeForBound.arity16]

-- The native gate's18 bound strictly exceeds the17 loop evaluations. This
-- does not purport to bound arbitrary library internals by an unrelated count.
theorem gate_bound : 17 < (18 : Nat) := by decide

#print axioms sufficient
#print axioms arity16
#print axioms gate_bound
end R1Z.ProverRw18ContextFuel
