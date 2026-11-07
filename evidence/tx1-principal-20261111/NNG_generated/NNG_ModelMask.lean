import NNG_InstallBase
import NNG_EmittedContext
import NLU_FieldValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelMask
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer outer_inverse)
open AspisR1.NMT_Transport (arr)

def call (low : Array Q 16#usize) (high : Alpha) (blind : Q) (alpha : Alpha) :=
  outer fromT1 (FIp_SemanticArithmetic.mask (arr toT1 low) (arr toT1 high) (toT1 blind) (arr toT1 alpha))

theorem call_model (low : Array Q 16#usize) (high : Alpha) (blind : Q) (alpha : Alpha) :
    outer toT1 (call low high blind alpha) =
      FIp_SemanticArithmetic.mask (arr toT1 low) (arr toT1 high) (toT1 blind) (arr toT1 alpha) :=
  outer_inverse fromT1 toT1 fromT1_inverse _
#print axioms call_model
end AspisR1.NNG_ModelMask
