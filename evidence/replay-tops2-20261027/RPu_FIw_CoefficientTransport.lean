import RPu_FIw_CoefficientMeaning
import R0P.Asset
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_CoefficientTransport
open FIq_Native
open FIv_NativeValue (K)
open FIw_CoefficientMeaning

def variant : Variant → R0P.Variant
  | .PrivateTransfer => .privateTransfer
  | .Withdrawal => .withdrawal

/-- The scalar-branch value is the model's exact two asset lanes. It does
not identify selector/opening/public inputs; those remain source joins. -/
theorem value (v : Variant) (present : Bool) (input output transfer withdrawal : K) :
    scalar v present input output transfer withdrawal=
      R0P.assetScalarLanes (variant v) present input output transfer withdrawal := by
  cases v <;> cases present <;>
    simp only [scalar,variant,R0P.assetScalarLanes,↓reduceIte,add_zero,Bool.false_eq_true]
#print axioms value
end AspisR1.FIw_CoefficientTransport
end
