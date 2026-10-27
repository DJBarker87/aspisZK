import RPu_PoseidonExternalPackedAlgebra
set_option autoImplicit false
namespace AspisR1.FJe_RawReference
open PoseidonExternalPackedAlgebra (packedNat)
open RawPoseidonExternalRows (rawRowNat)
open AspisV8R15.ExactTowerBase (P)
/-- The extra local-row bounds used in the isolated P6 context are DERIVED
from the full canonical input domain, not a restriction of that domain. -/
theorem row_bounds (w : Fin 4 → Fin 4 → Nat)
    (hw : ∀ r j,w r j<P) (r j : Fin 4) :
    rawRowNat (fun k=>w k j) r<7*P :=
  PoseidonExternalPackedAlgebra.raw_rows_lt_seven_P w hw r j
/-- Closed form of the owned raw packing reference, with exact signed-offset
order and fixed-width safety bound. No native loop is unfolded here. -/
theorem value (w : Fin 4 → Fin 4 → Nat) (hw : ∀ r j,w r j<P) :
    RawPoseidonRowField.decodeWords
      (packedNat (7*P) (fun r j=>rawRowNat (fun k=>w k j) r))=
      R0P.poseidonPackingFormula ExtractedMaskQmPackBase4Arithmetic.iBasis
        ExtractedMaskQmPackBase4Arithmetic.uBasis
        (R0P.poseidonMat4 (fun r=>RawPoseidonRowField.decodeWords (w r))) :=
  PoseidonExternalPackedAlgebra.packed_raw_rows_decode w hw

theorem output_bound (w : Fin 4 → Fin 4 → Nat) (hw : ∀ r j,w r j<P) (j : Fin 4) :
    packedNat (7*P) (fun r k=>rawRowNat (fun t=>w t k) r) j<8*(7*P) :=
  PoseidonExternalPackedAlgebra.packed_nat_lt_eight_bound _ _ (row_bounds w hw) j
#print axioms row_bounds
#print axioms value
#print axioms output_bound
end AspisR1.FJe_RawReference
