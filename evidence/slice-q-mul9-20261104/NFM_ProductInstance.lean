import NFM_Single
import NFI_WrapperTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFM_ProductInstance
open Aeneas Aeneas.Std Result

def mainProduct (a b : U32) : U64 :=
  U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
def tailProduct (a b : U64) : U64 := U64.wrapping_mul a b

theorem main_law : NFF_LoggedEight.Law mainProduct := by
  intro a b _ _
  have ca : (UScalar.cast .U64 a).val=a.val := by scalar_tac
  have cb : (UScalar.cast .U64 b).val=b.val := by scalar_tac
  change (U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)).val=
    (a.val*b.val)%2^64
  rw [U64.wrapping_mul_val_eq,ca,cb]
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]

theorem tail_law : NFF_ProductCall.Law tailProduct := by
  intro a b _ _
  change (U64.wrapping_mul a b).val=(a.val*b.val)%2^64
  rw [U64.wrapping_mul_val_eq]
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]

/-- Concrete product operations discharge both oracle laws. The remaining
canonical-g predicate concerns the actual caller argument, not a callee output. -/
theorem installed (input : NFI_InnerCut.Input)
    (canonical : NEV_DotInputs.Canonical input.g) :
    (NFM_Single.run mainProduct tailProduct input).result=
      FIp_NativeDots.fast_dots.four_dots_one input.q input.g input.slot :=
  NFM_Single.emitted mainProduct main_law tailProduct tail_law input canonical

theorem wrapper (q : Slice U8) (g : NEV_DotInputs.Coefficients) (qPlace gPlace : Nat)
    (canonical : NEV_DotInputs.Canonical g) :
    (NFI_WrapperTrace.run mainProduct tailProduct q g qPlace gPlace).result=
      NEI_FourWrapper.fast_dots.four_dots q g :=
  NFI_WrapperTrace.headline mainProduct main_law tailProduct tail_law q g qPlace gPlace canonical

#print axioms main_law
#print axioms tail_law
#print axioms installed
#print axioms wrapper
end AspisR1.NFM_ProductInstance
end
