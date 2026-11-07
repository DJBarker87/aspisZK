import NNG_LIBMaskHigh
import NNG_ModelMask
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBMask
open Aeneas Aeneas.Std Result NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)

theorem call_model (claims : LIB_VCarriers.Claims) (alpha : LIB_VCarriers.Alpha) :
    NNG_ModelMask.call (NNG_FromFnValues136.low (lowerClaims claims))
      (NNG_FromFnValues136.high (lowerClaims claims))
      (NNG_Array136.cell (lowerClaims claims) 27#usize (by decide)) (lowerArray alpha) =
      .ok (lower (LIB_VField.maskValue claims alpha)) := by
  unfold NNG_ModelMask.call
  rw [NNG_LIBMaskLow.low,NNG_LIBMaskHigh.high,NNG_LIBMaskCells.blind,NNG_LIBMaskCells.alpha,LIB_VField.mask_exact]
  rfl
#print axioms call_model

theorem projected (fallback : Value) (claims : LIB_VCarriers.Claims) (alpha : LIB_VCarriers.Alpha) :
    NNG_EmittedCallGraph.resultMap (project fallback)
      (NNG_ModelMask.call (NNG_FromFnValues136.low (lowerClaims claims))
        (NNG_FromFnValues136.high (lowerClaims claims))
        (NNG_Array136.cell (lowerClaims claims) 27#usize (by decide)) (lowerArray alpha)) =
      .ok (LIB_VField.maskValue claims alpha) := by
  rw [call_model]
  exact congrArg Result.ok (project_lower fallback _)
#print axioms projected
end AspisR1.NNG_LIBMask
