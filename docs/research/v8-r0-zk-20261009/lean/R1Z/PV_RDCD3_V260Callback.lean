import R1Z.PV_RDCD3_V260C_Exact
import R1Z.PV_RDCD3_V260

namespace R1Z.PV_RDCD3_V260Callback
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_B2_251c1
abbrev K := aspis_core.field.QM31

/-- Actual selected callback cohort: no dictionary is changed. -/
theorem source (w : host_weights.Weights) (kind j : Usize) :
    host_weights.raw_value w kind j = PV_RDCD3_V260C_Exact.original w kind j :=
  PV_RDCD3_V260C_Exact.source w kind j

/-- Uniform under the callback's existing fieldwise carrier conversion; failures
and divergence pass through, rather than an honest-run-only statement. -/
theorem carrier {B : Type} (decode : K → B) (w : host_weights.Weights) (kind j : Usize) :
    PV_RDCD3_V260.mapResult decode (host_weights.raw_value w kind j) =
      PV_RDCD3_V260.mapResult decode (PV_RDCD3_V260C_Exact.original w kind j) :=
  congrArg (PV_RDCD3_V260.mapResult decode) (source w kind j)

#print axioms source
#print axioms carrier
end R1Z.PV_RDCD3_V260Callback
