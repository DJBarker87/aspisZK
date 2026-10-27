import FJk_ResidualLane
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_ResidualPack
open FIv_NativeValue (K decode)
open FIw_ArrayValue (decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
attribute [local irreducible] R0P.poseidonLeadingPair
  R0P.poseidonInterpolatedFullPair R0P.poseidonInterpolatedInternalPair
/-- The explicit native packing is the packing of the SAME lane residual. -/
theorem value (o : Openings) (s : Selectors) (g : Fin 4) :
    FJh_Native07RawValue.model o s g =
      R0P.poseidonPackingFormula iBasis uBasis (fun j=>
        R0P.poseidonScalarResidual (FJh_Native07RawValue.openings o)
          (decode s.block) (decoded s.local) (FJe_ExternalAdjoint.lane g j)) := by
  unfold FJh_Native07RawValue.model
  rw [FJh_PackResidual.value]
  apply congrArg (R0P.poseidonPackingFormula iBasis uBasis)
  funext j
  have h := FJk_ResidualLane.value o s (FJe_ExternalAdjoint.lane g j)
  convert h using 1 <;> congr 2
#print axioms value
end AspisR1.FJk_ResidualPack
end
