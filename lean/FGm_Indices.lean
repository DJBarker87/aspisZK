import FGm_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_Indices
open Aeneas Aeneas.Std Result

def index (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩

theorem self (i : Usize) : index i.val=i := by
  apply UScalar.eq_of_val_eq
  simp only [index,UScalar.val,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt i.bv.isLt

#print axioms self
end AspisR1.FGm_Indices
end
