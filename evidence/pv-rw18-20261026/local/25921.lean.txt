import R1Z.ProverRw18FieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldModel
open Aeneas Aeneas.Std ProverRw18FieldMeaning

-- The usual field-polynomial meaning of the two-register arithmetic loop.
-- This component model is not the missing whole proof/audit model of V163.
def run : List U32 → K → K × K → K × K
  | [], _, state => state
  | value::values, lambda, (out,power) =>
    run values lambda (out+power*(value.val : K),power*lambda)

def eval : List U32 → K → K
  | [], _ => 0
  | value::values, lambda => (value.val : K)+lambda*eval values lambda

theorem append (left right : List U32) (lambda : K) (state : K × K) :
    run (left++right) lambda state=run right lambda (run left lambda state) := by
  induction left generalizing state with
  | nil => rfl
  | cons value values ih =>
    rcases state with ⟨out,power⟩
    exact ih (out+power*(value.val : K),power*lambda)

theorem output (values : List U32) (lambda : K) (state : K × K) :
    (run values lambda state).1=state.1+state.2*eval values lambda := by
  induction values generalizing state with
  | nil => simp only [run,eval,mul_zero,add_zero]
  | cons value values ih =>
    rcases state with ⟨out,power⟩
    rw [run,ih,eval]
    ring

theorem power (values : List U32) (lambda : K) (state : K × K) :
    (run values lambda state).2=state.2*lambda^values.length := by
  induction values generalizing state with
  | nil => simp only [run,List.length_nil,pow_zero,mul_one]
  | cons value values ih =>
    rcases state with ⟨out,power⟩
    rw [run,ih,List.length_cons,pow_succ]
    ring

#print axioms append
#print axioms output
#print axioms power
end R1Z.ProverRw18FieldModel
