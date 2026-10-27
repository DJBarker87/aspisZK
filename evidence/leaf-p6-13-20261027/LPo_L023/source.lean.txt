import LPo_B_LPc_DecodeValues
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPo.BC.Decode
/-- Successful actual model decoding establishes the canonical-producer domain. -/
theorem success_canonical (N : Usize) (r : r1_wire.ValidatedRecord) (offset : Usize)
    (out : Array aspis_core.field.QM31 N)
    (success : r1_wire.ValidatedRecord.decode_k N r offset = ok (.Ok out)) :
    ∀ q ∈ out.val, LPo.BA.Add.Canonical q := by
  rw [LPo.BA.Decode.shipped_leaf_model] at success
  dsimp only at success
  split at success
  · cases success
  · split at success
    · cases success
    · split at success
      · cases success
      · split at success
        · cases success
        · split at success
          · split at success <;> cases success
          · rename_i accepted
            split at success
            · cases success
              exact values_canonical _ _ _ accepted
            · cases success
#print axioms success_canonical
end LPo.BC.Decode
