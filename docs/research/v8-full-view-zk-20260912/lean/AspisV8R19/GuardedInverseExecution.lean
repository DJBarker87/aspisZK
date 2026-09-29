import AspisV8R19.GuardedM31Execution
import AspisV8R19.GeneratedInverseLoop

/-! Transport pointwise Result equality through the freshly extracted loop and
guarded inverse. No termination or canonical-output premise is added. -/
set_option autoImplicit false
namespace AspisV8R19.GuardedInverseExecution
open Aeneas Aeneas.Std Result AspisR64Field
open GuardedM31Execution InverseChain GeneratedInverseLoop

theorem body_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop.body r x =
      V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n_loop.body r x := by
  simp only [field.square_n_loop.body,
    V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n_loop.body,
    generated_mul_eq, Old.mul] <;> rfl

theorem loop_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop r x =
      V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n_loop r x := by
  simp only [field.square_n_loop,
    V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n_loop, body_eq]

theorem square_eq (x : U32) (count : Usize) :
    field.square_n x count =
      V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n x count := by
  simp only [field.square_n,
    V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n, loop_eq]

theorem inv_eq (x : U32) :
    field.M31.inv x = V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.inv x := by
  simp only [field.M31.inv,
    V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.inv,
    generated_mul_eq, Old.mul, square_eq]

theorem square_exec (x : Word) (count : Usize) :
    field.square_n (encode x) count = .ok (encode (squares wordMul count.val x)) := by
  rw [square_eq]
  exact square_n_exec x count

theorem zero_rejected : field.M31.inv 0#u32 = .fail .assertionFailure := by
  rw [inv_eq]
  exact inv_zero ⟨0, by decide⟩ rfl

theorem inverse_correct (x : U32) (hc : x.val < AspisV8R15.ExactTowerBase.P)
    (hne : x.val ≠ 0) :
    ∃ out : U32, field.M31.inv x = .ok out ∧ out.val < AspisV8R15.ExactTowerBase.P ∧
      (out.val : AspisV8R15.ExactTowerBase.M31Exact) =
        (x.val : AspisV8R15.ExactTowerBase.M31Exact)⁻¹ := by
  rw [inv_eq]
  exact inv_correct x hc hne

theorem entry_eq (x : U32) :
    inverse_probe x = V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.inv x := by
  simp only [inverse_probe, inv_eq]

#print axioms body_eq
#print axioms loop_eq
#print axioms square_eq
#print axioms inv_eq
#print axioms square_exec
#print axioms zero_rejected
#print axioms inverse_correct
#print axioms entry_eq
end AspisV8R19.GuardedInverseExecution
