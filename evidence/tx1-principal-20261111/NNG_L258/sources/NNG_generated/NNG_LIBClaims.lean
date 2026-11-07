import NNG_InstallClaims
import NNG_LIBArrays
import LIB_VClaims
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBClaims
open Aeneas Aeneas.Std Result NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)

def reservation (env : RSL.Env) : NP6_StdModel.Reservation :=
  if env.reservation then .Ok () else .Err ⟨.CapacityOverflow⟩

theorem raise_raw (value : LIB_VCarriers.Claims) :
    NNG_InstallClaims.raiseClaims (LIB_VCarriers.claimsRaw value) = lowerClaims value := by
  apply Subtype.ext
  simp only [NNG_InstallClaims.raiseClaims,LIB_VCarriers.claimsRaw,LIB_VCarriers.k29Raw,
    LIB_VScalarCarriers.array,lowerClaims,lowerArray,lower,arr,List.map_map,Function.comp_def]
#print axioms raise_raw

def call (env : RSL.Env) (p : NNG_verify_finish.r1_wire.Prefix) := NNG_InstallClaims.claims (reservation env) p

theorem call_model (env : RSL.Env) (p : LIB_VCarriers.Prefix) :
    call env (fromT12 (LIB_VCarriers.prefixRaw p)) =
      .ok (if env.reservation then .Ok (lowerClaims (LIB_VClaims.value p)) else .Err .Allocation) := by
  unfold call NNG_InstallClaims.claims
  rw [fromT12_inverse]
  cases h : env.reservation with
  | false =>
    simp only [reservation,h,Bool.false_eq_true,if_false,LIB_VClaims.error_exact]
    rfl
  | true =>
    simp only [reservation,h,if_true,LIB_VClaims.success_exact]
    change Result.ok (.Ok (NNG_InstallClaims.raiseClaims (LIB_VCarriers.claimsRaw (LIB_VClaims.value p)))) = _
    rw [raise_raw]
#print axioms call_model

def projectReply (fallback : Value) :
    NNG_verify_finish.core.result.Result Claims NNG_verify_finish.r1_wire.Error → Except LIB_VCarriers.WErr LIB_VCarriers.Claims
  | .Ok c => .ok (projectClaims fallback c)
  | .Err e => .error (toT13 e)

theorem projected (fallback : Value) (env : RSL.Env) (p : LIB_VCarriers.Prefix) :
    NNG_EmittedCallGraph.resultMap (projectReply fallback) (call env (fromT12 (LIB_VCarriers.prefixRaw p))) =
      .ok (LIB_VClaims.eval p env) := by
  rw [call_model]
  cases h : env.reservation <;>
    simp only [h,if_true,Bool.false_eq_true,if_false,NNG_EmittedCallGraph.resultMap,
      projectReply,LIB_VClaims.eval,project_lower_claims,toT13]
#print axioms projected
end AspisR1.NNG_LIBClaims
