import NNG_LIBRecords
import LIB_VArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBRoundProjection
open Aeneas Aeneas.Std NNG_Transport NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)

theorem scalar (fallback : Value) (q : LIB_VScalarCarriers.RawQ) (canonical : LIB_VScalarCarriers.CanonicalRaw q) :
    project fallback (fromT1 q) = LIB_VScalarCarriers.ofRaw q canonical := by
  have raised : fromT1 q = lower (LIB_VScalarCarriers.ofRaw q canonical) := by
    unfold lower
    rw [LIB_VScalarCarriers.toRaw_ofRaw]
  rw [raised,project_lower]
#print axioms scalar

theorem array {n : Usize} (fallback : Value) (a : Array LIB_VScalarCarriers.RawQ n)
    (canonical : LIB_VArray.Canonical a) :
    projectArray fallback (arr fromT1 a) = LIB_VArray.lift a canonical := by
  have raised := NNG_LIBRecords.raise_array (LIB_VArray.lift a canonical)
  rw [LIB_VArray.raw_lift] at raised
  rw [raised,project_lower_array]
#print axioms array
end AspisR1.NNG_LIBRoundProjection
