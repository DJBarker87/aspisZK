import S9PrivateScaledBaseModelV1
import S9QuadraticFieldMulProjectionV1
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AspisR1S9PrivateFieldDotTransportV1
open AspisR1S9QuadraticFieldMulProjectionV1
abbrev E := AspisWideTower.WideExact
/-- Exact definition/proof reused from the already-green Point operator API,
renamed into this smaller actual-private source context. -/
def fieldSum {I K : Type} [Field K] (s : Finset I) (f : I → K) : K := ∑i∈s,f i

theorem sum_operator_eq {I : Type} (s : Finset I) (f : I → E) :
    (∑i∈s,f i)=fieldSum s f := by rfl

theorem mul_operator_eq (x y : E) : x*y=projectedMul x y := by
  exact (quadratic_field_mul AspisWideTower.wideU 0 x y).symm

def fieldDot {I K : Type} [Fintype I] [Field K] (f c : I → K) : K := ∑i,f i*c i

theorem generic_dot_api {I K : Type} [Fintype I] [Field K] (f c : I → K) :
    fieldSum Finset.univ (fun i=>projectedMul (f i) (c i))=fieldDot f c := rfl

/-- All functions and index types stay opaque: inherited additive and
multiplicative dictionary transport, not enumeration or field algebra. -/
theorem native_dot_operator_eq {I : Type} [Fintype I] (f c : I → E) :
    (∑i,f i*c i)=fieldDot f c := by
  have hp : (fun i=>f i*c i)=(fun i=>projectedMul (f i) (c i)) :=
    funext (fun i=>mul_operator_eq (f i) (c i))
  have hs := sum_operator_eq Finset.univ (fun i=>f i*c i)
  exact hs.trans ((congrArg (fieldSum Finset.univ) hp).trans (generic_dot_api f c))

/-- Name the entire generic private finite sum before specializing its field. -/
theorem generic_private_dot_api {K : Type} [Field K] (a0 a1 q0 q1 : K) (input : Fin 64 → K) :
    fieldDot (fun j : Fin 4=>input (Fin.castAdd 60 j))
      (fun j=>AspisR1.S2LibraFactoredIdentity.original
        (AspisR1.S2LibraFactoredIdentity.scaled (AspisR1S9TwoDualSourceBaseV1.powers a0)
          AspisR1.RoundPairing.quarter)
        (AspisR1.S2LibraFactoredIdentity.scaled (AspisR1S9TwoDualSourceBaseV1.powers a1)
          AspisR1.RoundPairing.quarter) q0 q1 j)=
      AspisR1.RoundPairing.dot input
        (AspisR1.RoundPairing.dualFold a1 (AspisR1.RoundPairing.dualFold a0
          (AspisR1S9TwoDualSourcePrivateV1.privateRow q0 q1))) := by
  exact (AspisR1S9TwoDualSourcePrivateV1.private_two_dual_dot_original a0 a1 q0 q1 input).symm

#print axioms sum_operator_eq
#print axioms mul_operator_eq
#print axioms generic_dot_api
#print axioms native_dot_operator_eq
#print axioms generic_private_dot_api
end AspisR1S9PrivateFieldDotTransportV1
end
