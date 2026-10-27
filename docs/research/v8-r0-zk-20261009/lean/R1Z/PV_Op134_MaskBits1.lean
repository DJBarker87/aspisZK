import R1Z.PV_Op134_Masks
import R1Z.PV_Op134_RowSpec
namespace R1Z.PV_Op134_MaskBits1
open Aeneas Aeneas.Std
set_option autoImplicit false
-- Only 8 blocks x 16 bit positions are evaluated; no large Finset.univ.
theorem bits : ∀ block : Fin 8, ∀ bit : Fin 16,
    Nat.testBit (PV_Op134_Masks.masks.val[8+block.val]'(by
      rw [PV_Op134_Masks.length]; have := block.isLt; omega)).val bit.val = true ↔
      16*(8+block.val)+bit.val ∈ PV_Op134_RowSpec.rows.map (fun r => r.val) := by decide
#print axioms bits
end R1Z.PV_Op134_MaskBits1
