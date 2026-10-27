import RPu_FJk_Native07Value
import RPu_PoseidonResidualFieldTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_ResidualWide
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open FIz_ConcretePack (embed)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- Scalar residual transport into Wide, on the very same input cells. -/
theorem scalar (o : Openings) (s : Selectors) (lane : Fin 16) :
    embed (R0P.poseidonScalarResidual (FJh_Native07RawValue.openings o)
      (decode s.block) (decoded s.local) lane)=
    R0P.poseidonScalarResidual
      (ValueFamilyFieldTransport.mapOpenings embed (FJh_Native07RawValue.openings o))
      (embed (decode s.block)) (fun i=>embed (decoded s.local i)) lane := by
  exact PoseidonResidualFieldTransport.map_scalarResidual embed _ _ _ _
#print axioms scalar
end AspisR1.FJk_ResidualWide
end
