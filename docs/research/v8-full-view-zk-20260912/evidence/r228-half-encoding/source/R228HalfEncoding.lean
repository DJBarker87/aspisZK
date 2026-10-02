import AspisV8R19.R224HalfWordBounds
import AspisV8R19.R225LineNormAlgebra
import AspisV8R19.R163ComplexExecution

/-! Canonical half-word algebra for connecting source half execution.
This file does not itself bind a source half declaration. -/
set_option autoImplicit false
namespace AspisV8R19.R228HalfEncoding
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val eq_encodeBase)
noncomputable section

def halfScalar (w : U32) : U32 := ⟨R224HalfWordBounds.halfWord w.bv⟩

theorem halfScalar_canonical (w : U32) (h : w.val < P) :
    (halfScalar w).val < P := by
  exact R224HalfWordBounds.canonical w.bv h

theorem halfScalar_double (w : U32) (h : w.val < P) :
    2*(halfScalar w).val=w.val+(w.val%2)*P := by
  exact R224HalfWordBounds.double_value w.bv h

theorem base_two_nonzero : (2 : M31Exact) ≠ 0 := by decide

theorem halfScalar_encode (x : M31Exact) :
    halfScalar (encodeBase x) = encodeBase (x/2) := by
  have hc := halfScalar_canonical (encodeBase x) (ZMod.val_lt x)
  have hd := halfScalar_double (encodeBase x) (ZMod.val_lt x)
  apply eq_encodeBase _ _ hc
  apply (eq_div_iff base_two_nonzero).2
  have he := congrArg (fun n : Nat => (n : M31Exact)) hd
  simp only [Nat.cast_mul,Nat.cast_add,encodeBase_val,ZMod.natCast_zmod_val] at he
  have hp : (P : M31Exact) = 0 := by simp [M31Exact,P]
  rw [hp,mul_zero,add_zero] at he
  simpa only [Nat.cast_ofNat,mul_comm] using he

#print axioms halfScalar_canonical
#print axioms halfScalar_double
#print axioms base_two_nonzero
#print axioms halfScalar_encode
end
end AspisV8R19.R228HalfEncoding
