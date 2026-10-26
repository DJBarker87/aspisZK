import R1Z.ProverRw18ContextBranch
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextErrors
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes] [ExternalFuns]

-- In particular these hold when i is the final active element. Returning
-- the accumulator early would be unsound for these complete Result laws.
theorem power_failure (lambda : Q) (values : Slice U32) (i : Nat)
    (active : i<values.val.length) (out power scaled out1 : Q) (error : Error)
    (scale : aspis_core.field.QM31.mul_m31 power values.val[i]=ok scaled)
    (add : aspis_core.field.QM31.add out scaled=ok out1)
    (mul : aspis_core.field.QM31.mul power lambda=.fail error) :
    run lambda (⟨values,i⟩ : Iter) out power=.fail error := by
  rw [ProverRw18ContextBranch.some lambda values i active,scale]
  simp only [bind_tc_ok,add,mul]
  rfl

theorem power_divergence (lambda : Q) (values : Slice U32) (i : Nat)
    (active : i<values.val.length) (out power scaled out1 : Q)
    (scale : aspis_core.field.QM31.mul_m31 power values.val[i]=ok scaled)
    (add : aspis_core.field.QM31.add out scaled=ok out1)
    (mul : aspis_core.field.QM31.mul power lambda=.div) :
    run lambda (⟨values,i⟩ : Iter) out power=.div := by
  rw [ProverRw18ContextBranch.some lambda values i active,scale]
  simp only [bind_tc_ok,add,mul]
  rfl

theorem scale_failure (lambda : Q) (values : Slice U32) (i : Nat)
    (active : i<values.val.length) (out power : Q) (error : Error)
    (scale : aspis_core.field.QM31.mul_m31 power values.val[i]=.fail error) :
    run lambda (⟨values,i⟩ : Iter) out power=.fail error := by
  rw [ProverRw18ContextBranch.some lambda values i active,scale]
  rfl

theorem add_failure (lambda : Q) (values : Slice U32) (i : Nat)
    (active : i<values.val.length) (out power scaled : Q) (error : Error)
    (scale : aspis_core.field.QM31.mul_m31 power values.val[i]=ok scaled)
    (add : aspis_core.field.QM31.add out scaled=.fail error) :
    run lambda (⟨values,i⟩ : Iter) out power=.fail error := by
  rw [ProverRw18ContextBranch.some lambda values i active,scale]
  simp only [bind_tc_ok,add]
  rfl

#print axioms power_failure
#print axioms power_divergence
#print axioms scale_failure
#print axioms add_failure
end R1Z.ProverRw18ContextErrors
