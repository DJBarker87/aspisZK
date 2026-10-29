import JFn_LineTotal
import SAQ_RawWide
import NEA_FoldModel
set_option autoImplicit false
noncomputable section
namespace NEA_CurrentProducts
open Aeneas Aeneas.Std Result AspisR1
open AspisR1CurrentWide AspisR1CurrentWide.Proof

theorem wide (x y : E) (hx : CanonicalWide x) (hy : CanonicalWide y) :
    ∃ z, field.wide_exact.WideExact.mul x y=ok z ∧ CanonicalWide z ∧
      decodeWide z=decodeWide x*decodeWide y := by
  obtain ⟨z,run,canonical,_⟩ := wide_mul_total_exact x y hx hy
  exact ⟨z,run,canonical,(SAQ_RawWide.mul_exact x y z run).2⟩

theorem scale (x : E) (s : U32) :
    ∃ z, field.wide_exact.WideExact.mul_m31 x s=ok z ∧ CanonicalWide z ∧
      decodeWide z=decodeWide x*SAQ_RawScale.wideScalarEmbedding s := by
  obtain ⟨z,run,canonical⟩ := JFn_ScaleTotal.wide x s
  exact ⟨z,run,canonical,(SAQ_RawScale.wide_mul_m31_success x z s run).2⟩

theorem base (x y : U32) :
    ∃ z, field.M31.mul x y=ok z ∧ z.val<2147483647 ∧
      z.val=(x.val*y.val)%2147483647 := by
  obtain ⟨z,run,value,canonical⟩ := ExtractedCurrentReducer.current_mul_mod x y
  exact ⟨z,by rw [m31_mul_same];exact run,canonical,value⟩

#print axioms wide
#print axioms scale
#print axioms base
end NEA_CurrentProducts
end
