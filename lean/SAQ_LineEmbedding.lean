import SAQ_RawScale
import SAQ_RawWide
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineEmbedding
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof
abbrev FP := ZMod AspisCircleGroupOrder.P
abbrev FE := AspisWideTower.WideExact
def decode (x : U32) : FP := x.val

theorem scale (x z : E) (s : U32) (h : field.wide_exact.WideExact.mul_m31 x s=ok z) :
    CanonicalWide z ∧ decodeWide z=decodeWide x * algebraMap FP FE (decode s) := by
  have result := SAQ_RawScale.wide_mul_m31_success_algebraMap x z s h
  exact result

theorem baseMul (x y z : U32) (h : field.M31.mul x y=ok z) :
    z.val<2147483647 ∧ decode z=decode x*decode y := by
  rw [m31_mul_same] at h
  exact ⟨R17CurrentDomainCanonical.mul_success_canonical x y z h,
    R17CurrentM31Semantics.current_mul_decode x y z h⟩

#print axioms scale
#print axioms baseMul
end AspisR1.SAQ_LineEmbedding
end
